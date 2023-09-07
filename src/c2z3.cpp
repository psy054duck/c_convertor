#include "c2z3.h"
#include <stdexcept>
#include <algorithm>
#include <iterator>

class UnimplementedOperationException: public std::runtime_error {
    public:
        UnimplementedOperationException(int opcode): runtime_error(Instruction::getOpcodeName(opcode)) {}
};

std::string get_validation_type_name(validation_type ty) {
    std::string res;
    switch (ty) {
        case correct: res = "correct"; break;
        case wrong  : res = "wrong"  ; break;
        default     : res = "unknown"; break;
    }
    return res;
}

void combine_vec(z3::expr_vector& v1, z3::expr_vector& v2) {
    for (auto i : v2) {
        v1.push_back(i);
    }
}

c2z3::c2z3(std::unique_ptr<Module> &mod): m(std::move(mod)), rec_s(z3ctx), expression2solve(z3ctx) {
    // Register all the basic analyses with the managers.
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    ModulePassManager MPM;
    MPM.addPass(createModuleToFunctionPassAdaptor(PromotePass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(LCSSAPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(SimplifyCFGPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(LoopSimplifyPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(InstructionNamerPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(AggressiveInstCombinePass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(MemorySSAWrapperPass()));

    MPM.run(*m, MAM);


    std::error_code ec;
    raw_fd_ostream output_fd("tmp/tmp.ll", ec);
    m->print(output_fd, NULL);
    output_fd.close();
    auto &fam = MAM.getResult<FunctionAnalysisManagerModuleProxy>(*m).getManager();
    for (auto F = m->begin(); F != m->end(); F++) {
        if (!F->isDeclaration()) {
            LoopInfo& LI = fam.getResult<LoopAnalysis>(*F);
            MemorySSA& MSSA = fam.getResult<MemorySSAAnalysis>(*F).getMSSA();
            DominatorTree DT = DominatorTree(*F);
            PostDominatorTree PDT = PostDominatorTree(*F);
            // LIs[&*F] = LI;
            LIs.emplace(&*F, LI);
            DTs.emplace(&*F, DominatorTree(*F));
            PDTs.emplace(&*F, PostDominatorTree(*F));
            MSSAs.emplace(&*F, MSSA);
            // MSSAs.insert_or_assign(&*F, MSSA);
            if (F->getName() == "main") {
                main = &*F;
            }
        }
    }
    get_loop_idx();
}

use_vector c2z3::getAllAssertions() {
    use_vector res;
    for (auto& bb : *main) {
        for (auto& ins : bb) {
            if (auto call = dyn_cast_or_null<CallInst>(&ins)) {
                Function* f = call->getCalledFunction();
                if (f && f->getName().endswith("assert")) {
                    assert(call->arg_size() == 1);
                    res.push_back(&call->getArgOperandUse(0));
                }
            }
        }
    }
    return res;
}

std::set<PHINode*> c2z3::get_header_defs(Value* v) {
    // get phi nodes in header that v depends directly/indirectly on
    std::set<PHINode*> res;
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(inst->getParent());
    BasicBlock* header = loop->getHeader();
    if (auto phi = dyn_cast_or_null<PHINode>(v)) {
        if (phi->getParent() == header) {
            return {phi};
        }
    }
    for (int i = 0; i < inst->getNumOperands(); i++) {
        Value* operand = inst->getOperand(i);
        auto operand_inst = dyn_cast_or_null<Instruction>(operand);
        if (operand_inst && loop->contains(operand_inst))
            res.merge(get_header_defs(operand));
    }
    return res;
}

rec_ty c2z3::header_phi_as_rec(PHINode* phi) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(phi->getParent());
    BasicBlock* latch = loop->getLoopLatch();
    Value* rec_v = phi->getIncomingValueForBlock(latch);
    z3::expr rec_z3 = express_v_as_header_phis(rec_v);
    z3::expr rec_def = v2z3(phi, loop->getLoopDepth(), true);
    rec_ty res;
    res.insert_or_assign(rec_def, rec_z3);
    return res;
}

initial_ty c2z3::header_phi_as_initial(PHINode* phi) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(phi->getParent());
    int dim = loop->getLoopDepth();
    z3::func_decl f = get_z3_function(phi, dim);
    z3::expr_vector args = get_args(dim, false, false, false);
    args.pop_back();
    args.push_back(z3ctx.int_val(0));
    rec_ty res;
    BasicBlock* initial_bb = phi->getIncomingBlock(0);
    if (initial_bb == loop->getLoopLatch()) initial_bb = phi->getIncomingBlock(1);
    int dim_initial = LI.getLoopDepth(initial_bb);
    int operand_idx = phi->getBasicBlockIndex(initial_bb);
    // z3::expr initial_v = v2z3(phi->getIncomingValueForBlock(initial_bb), dim_initial, false);
    z3::expr initial_v = use2z3(&phi->getOperandUse(operand_idx));
    // res.insert_or_assign(f(args), initial_v);
    z3::expr_vector fs(z3ctx);
    z3::expr_vector vs(z3ctx);
    fs.push_back(f(args));
    vs.push_back(initial_v);
    return {fs, vs};
}

z3::expr c2z3::express_v_as_header_phis(Value* v) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(inst->getParent());
    return _express_v_as_header_phis(v, loop);
}

z3::expr c2z3::_express_v_as_header_phis(Value* v, Loop* inner_loop) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        int svalue = CI->getSExtValue();
        return is_bool(v) ? z3ctx.bool_val(svalue) : z3ctx.int_val(svalue);
    }
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    BasicBlock* bb = inst->getParent();
    Loop* loop = LI.getLoopFor(bb);
    int dim = LI.getLoopDepth(bb);
    if (loop != inner_loop) {
        return v2z3(v, dim, false);
    }
    if (bb == loop->getHeader() && isa<PHINode>(v)) {
        return v2z3(v, dim, false);
    }
    z3::func_decl f = get_z3_function(v, dim);
    z3::expr_vector args = get_args(dim, false, false, false);
    z3::expr_vector res(z3ctx);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = _express_v_as_header_phis(op0, inner_loop);
        z3::expr z3op1 = _express_v_as_header_phis(op1, inner_loop);
        if (opcode == Instruction::Add) {
            return z3op0 + z3op1;
        } else if (opcode == Instruction::Sub) {
            return z3op0 - z3op1;
        } else if (opcode == Instruction::Mul) {
            return z3op0 * z3op1;
        } else if (opcode == Instruction::SDiv || opcode == Instruction::UDiv) {
            return z3op0 / z3op1;
        } else if (opcode == Instruction::SRem || opcode == Instruction::URem) {
            return z3op0 % z3op1;
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else if (opcode == Instruction::ICmp) {
        auto CI = dyn_cast<ICmpInst>(inst);
        auto pred = CI->getPredicate();
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = _express_v_as_header_phis(op0, inner_loop);
        z3::expr z3op1 = _express_v_as_header_phis(op1, inner_loop);
        if (pred == ICmpInst::ICMP_EQ) {
            return z3op0 == z3op1;
        } else if (pred == ICmpInst::ICMP_NE) {
            return z3op0 != z3op1;
        } else if (ICmpInst::isLT(pred)) {
            return z3op0 < z3op1;
        } else if (ICmpInst::isLE(pred)) {
            return z3op0 <= z3op1;
        } else if (ICmpInst::isGT(pred)) {
            return z3op0 > z3op1;
        } else if (ICmpInst::isGE(pred)) {
            return z3op0 >= z3op1;
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else if (auto CI = dyn_cast_or_null<SelectInst>(inst)) {
        z3::expr cond = _express_v_as_header_phis(CI->getOperand(0), inner_loop);
        z3::expr first = _express_v_as_header_phis(CI->getOperand(1), inner_loop);
        z3::expr second = _express_v_as_header_phis(CI->getOperand(2), inner_loop);
        return z3::ite(cond, first, second);
    } else if (auto CI = dyn_cast_or_null<CallInst>(inst)) {
        // all calls are treated as unknown values;
        return z3ctx.int_const("unknown");
    } else if (auto CI = dyn_cast_or_null<PHINode>(inst)) {
        z3::expr ite = phi2ite_header(CI);
        if (ite) {
            return ite;
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else {
        throw UnimplementedOperationException(opcode);
    }
    // z3::expr final_res = z3ctx.bool_val(true);
    // for (auto e : res) {
    //     final_res = final_res && e;
    // }
    // return final_res;
}

z3::expr c2z3::phi2ite_header(PHINode* phi) {
    DominatorTree& DT = DTs.at(main);
    PostDominatorTree& PDT = PDTs.at(main);
    assert(phi->getNumIncomingValues() == 2);
    BasicBlock* bb0 = phi->getIncomingBlock(0);
    BasicBlock* bb1 = phi->getIncomingBlock(1);
    BasicBlock* merge_bb = DT.findNearestCommonDominator(bb0, bb1);
    BasicBlock* curB = phi->getParent();
    LoopInfo& LI = LIs.at(main);
    int dim = LI.getLoopDepth(curB);
    if (PDT.dominates(curB, merge_bb)) {
        const Instruction* term = merge_bb->getTerminator();
        const BranchInst* branch = dyn_cast<BranchInst>(term);
        if (branch && branch->isConditional()) {
            Value* condV = branch->getCondition();
            const BasicBlock* true_b = bb0;
            const BasicBlock* false_b = bb1;
            if (DT.dominates(branch->getSuccessor(0), bb0) || DT.dominates(branch->getSuccessor(1), bb1)) {
                true_b = bb0;
                false_b = bb1;
            } else {
                true_b = bb1;
                false_b = bb0;
            }
            int true_idx = phi->getBasicBlockIndex(true_b);
            int false_idx = phi->getBasicBlockIndex(false_b);
            // z3::expr cond = v2z3(condV, dim, false);
            z3::expr cond = express_v_as_header_phis(condV);
            z3::expr v0 = express_v_as_header_phis(phi->getIncomingValue(true_idx));
            z3::expr v1 = express_v_as_header_phis(phi->getIncomingValue(false_idx));
            // z3::expr v0 = v2z3(phi->getIncomingValue(true_idx), dim, false);
            // z3::expr v1 = v2z3(phi->getIncomingValue(false_idx), dim, false);
            return z3::ite(cond, v0, v1);
            // Value* new_select = builder.CreateSelect(condV, phi->getIncomingValue(true_idx), phi->getIncomingValue(false_idx));
            // new_select->setName(v->getName());
            // inst = dyn_cast<Instruction>(new_select);
        }
    }
    return z3ctx.bool_val(false);
}

z3::expr_vector c2z3::get_pure_args(int dim, bool c) {
    z3::expr_vector res(z3ctx);
    for (int i = 0; i < dim; i++) {
        std::string idx = "n" + std::to_string(i);
        if (c) {
            idx = "N" + std::to_string(i);
        }
        res.push_back(z3ctx.int_const(idx.data()));
    }
    return res;
}

rec_ty c2z3::loop2rec(Loop* loop) {
    BasicBlock* header = loop->getHeader();
    rec_ty total_recs;
    for (auto& phi : header->phis()) {
        rec_ty phi_rec = header_phi_as_rec(&phi);

        total_recs.insert(phi_rec.begin(), phi_rec.end());
    }
    // for (auto r : total_recs) {
    //     errs() << r.first.to_string() << " = " << r.second.to_string() << "\n";
    // }
    // errs() << "**************\n";
    return total_recs;
}

initial_ty c2z3::loop2initial(Loop* loop) {
    BasicBlock* header = loop->getHeader();
    z3::expr_vector ks(z3ctx);
    z3::expr_vector vs(z3ctx);
    for (auto& phi : header->phis()) {
        initial_ty phi_initial = header_phi_as_initial(&phi);
        combine_vec(ks, phi_initial.first);
        combine_vec(vs, phi_initial.second);
        // total_initial.insert(phi_initial.begin(), phi_initial.end());
    }
    return {ks, vs};
}

z3::expr_vector c2z3::inst2z3(Instruction* inst, BasicBlock* prev_bb=nullptr) {
    z3::expr_vector res(z3ctx);
    if (auto CI = dyn_cast_or_null<CallInst>(inst)) {
        return res;
    }
    Type* tp = inst->getType();
    const char* var_name = inst->getName().data();
    bool is_bool = tp->isIntegerTy(1);
    LoopInfo& LI = LIs.at(main);
    BasicBlock* block = inst->getParent();
    Loop* loop = LI.getLoopFor(block);
    int dim = LI.getLoopDepth(block);
    
    z3::expr_vector loop_args = get_pure_args(dim, false);
    z3::expr_vector initial_res(z3ctx);
    z3::func_decl f = get_z3_function(inst, dim);
    z3::expr_vector args = get_args(dim, false, true, false);
    bool solved = false;
    int opcode = inst->getOpcode();
    if (solved) {
        // pass
    } else if (inst->isBinaryOp()) {
        Use& op0 = inst->getOperandUse(0);
        Use& op1 = inst->getOperandUse(1);
        z3::expr z3op0 = use2z3(&op0);
        z3::expr z3op1 = use2z3(&op1);
        if (opcode == Instruction::Add) {
            res.push_back(f(args) == z3op0 + z3op1);
        } else if (opcode == Instruction::Sub) {
            res.push_back(f(args) == z3op0 - z3op1);
        } else if (opcode == Instruction::Mul) {
            res.push_back(f(args) == z3op0 * z3op1);
        } else if (opcode == Instruction::SDiv || opcode == Instruction::UDiv) {
            res.push_back(f(args) == z3op0 / z3op1);
        } else if (opcode == Instruction::SRem || opcode == Instruction::URem) {
            res.push_back(f(args) == z3op0 % z3op1);
        } else if (opcode == Instruction::And) {
            res.push_back(f(args) == z3op0 && z3op1);
        } else if (opcode == Instruction::Or) {
            res.push_back(f(args) == z3op0 || z3op1);
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else if (opcode == Instruction::ICmp) {
        auto CI = dyn_cast_or_null<ICmpInst>(inst);
        auto pred = CI->getPredicate();
        Use& op0 = inst->getOperandUse(0);
        Use& op1 = inst->getOperandUse(1);
        z3::expr z3op0 = use2z3(&op0);
        z3::expr z3op1 = use2z3(&op1);
        if (pred == ICmpInst::ICMP_EQ) {
            res.push_back(f(args) == (z3op0 == z3op1));
        } else if (pred == ICmpInst::ICMP_NE) {
            res.push_back(f(args) == (z3op0 != z3op1));
        } else if (ICmpInst::isLT(pred)) {
            res.push_back(f(args) == (z3op0 < z3op1));
        } else if (ICmpInst::isLE(pred)) {
            res.push_back(f(args) == (z3op0 <= z3op1));
        } else if (ICmpInst::isGT(pred)) {
            res.push_back(f(args) == (z3op0 > z3op1));
        } else if (ICmpInst::isGE(pred)) {
            res.push_back(f(args) == (z3op0 >= z3op1));
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else if (auto CI = dyn_cast_or_null<SelectInst>(inst)) {
        z3::expr cond = use2z3(&CI->getOperandUse(0));
        z3::expr first = use2z3(&CI->getOperandUse(1));
        z3::expr second = use2z3(&CI->getOperandUse(2));
        res.push_back(f(args) == z3::ite(cond, first, second));
    } else if (auto CI = dyn_cast_or_null<CallInst>(inst)) {
        // all calls are treated as unknown values;
        Function* called = CI->getCalledFunction();
        auto called_name = called->getName();
        if (called_name.endswith("uint")) {
            res.push_back(f(args) >= 0);
        }
    } else if (auto CI = dyn_cast_or_null<PHINode>(inst)) {
        if (prev_bb) {
            int idx = CI->getBasicBlockIndex(prev_bb);
            Use* instantiated = &CI->getOperandUse(idx);
            z3::expr z3_instantiated = use2z3(instantiated);
            res.push_back(f(args) == z3_instantiated);
        } else {
            for (int i = 0; i < CI->getNumIncomingValues(); i++) {
                BasicBlock* cur_bb = inst->getParent();
                BasicBlock* in_bb = CI->getIncomingBlock(i);
                Use* op = &CI->getOperandUse(i);
                z3::expr z3_op = use2z3(op);
                // phi in header
                if (loop && loop->getHeader() == block) {
                    std::string n_idx = "n" + std::to_string(dim - 1);
                    std::string N_idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(dim - 1);
                    z3::expr z3_nidx = z3ctx.int_const(n_idx.data());
                    z3::expr z3_Nidx = z3ctx.int_const(N_idx.data());
                    if (!loop->contains(in_bb)) {
                        // initial
                        // args[dim - 1] = z3ctx.int_val(0);
                        args.pop_back();
                        args.push_back(z3ctx.int_val(0));
                        initial_res.push_back(f(args) == z3_op);
                    } else if (loop->getLoopLatch() == in_bb) {
                        // inductive
                        args.pop_back();
                        args.push_back(z3_nidx + 1);
                        // args[dim - 1] = z3_nidx + 1;
                        // res.push_back(z3::implies(z3_nidx >= 0, f(args) == z3_op));
                        res.push_back(f(args) == z3_op);
                    } else {
                        throw UnimplementedOperationException(opcode);
                    }
                } else {
                    pc_type pc = path_condition(in_bb);
                    z3::expr cond = pc.first; 
                    // z3::expr cond = path_condition(in_bb);
                    // z3::expr local_cond = path_condition_b2b(in_bb, cur_bb);
                    auto cond_negated = path_condition_b2b(in_bb, cur_bb);
                    z3::expr local_cond = use2z3(cond_negated.first);
                    Loop* prev_loop = LI.getLoopFor(in_bb);
                    if (prev_loop && prev_loop->contains(cur_bb)) {
                        local_cond = cond_negated.second ? !local_cond : local_cond;
                    } else if (prev_loop) {
                        int prev_dim = LI.getLoopDepth(prev_loop->getHeader());
                        z3::expr_vector N_args = get_args(prev_dim, true, false, true, prev_loop);
                        z3::expr_vector n1_args = get_args(prev_dim, false, true, true);
                        local_cond = cond_negated.second ? !local_cond : local_cond;
                        local_cond = local_cond.simplify().substitute(n1_args, N_args);
                        cond = cond.simplify().substitute(n1_args, N_args);
                    } else {
                        local_cond = z3ctx.bool_val(true);
                    }
                    res.push_back(z3::implies(cond && local_cond, f(args) == z3_op));
                }
            }
        }
    } else if (auto CI = dyn_cast_or_null<AllocaInst>(inst)) {
        Type* ty = CI->getAllocatedType();
        ArrayType* arr_ty = dyn_cast_or_null<ArrayType>(ty);
        errs() << arr_ty->getNumElements() << "\n";
        errs() << arr_ty->getElementType()->isArrayTy() << "\n";
        arr_ty->getElementType()->print(errs());
        errs() << "\n";
    } else if (auto CI = dyn_cast_or_null<LoadInst>(inst)) {
        MemorySSA& MSSA = MSSAs.at(main);
        MemoryUseOrDef* mud = MSSA.getMemoryAccess(inst);
        MemoryAccess* def_acc = mud->getDefiningAccess();
        MemorySSAWalker* walker = MSSA.getWalker();
        MemoryAccess* clobber = walker->getClobberingMemoryAccess(inst);
        // if (auto m_phi = dyn_cast_or_null<MemoryPhi>(clobber)) {
        //     m_phi->print(errs());
        // } else if (auto m_def_use = dyn_cast_or_null<MemoryUseOrDef>(clobber)) {
        //     m_def_use->print(errs());
        // }
        // mud->getMemoryInst()->print(errs());
        // errs() << "\n";
        // mud->print(errs());
        // errs() << "\n";
        // def_acc->print(errs());
        // errs() << "\n";
        // for (auto def = def_acc->defs_begin(); def != def_acc->defs_end(); def++) {
        //     def->get
        // }
        Value* pointer = CI->getPointerOperand();
        GetElementPtrInst* arr_ptr = dyn_cast_or_null<GetElementPtrInst>(pointer);
        assert(arr_ptr);
        Value* arr = arr_ptr->getPointerOperand();
        assert(isa<AllocaInst>(arr));
        // errs() << inst->getName() << "\n";
        // errs() << arr->getName() << "\n";
    } else if (auto CI = dyn_cast_or_null<SExtInst>(inst)) {
        res.push_back(f(args) == use2z3(&CI->getOperandUse(0)));
    } else {
        throw UnimplementedOperationException(opcode);
    }
    // return res;
    // return z3::forall(params, res);
    z3::expr_vector forall_res(z3ctx);
    z3::expr loop_range = z3ctx.bool_val(true);
    for (auto a : loop_args) {
        loop_range = loop_range && a >= 0;
    }
    // loop_range.simplify();
    for (auto e : res) {
        if (loop_args.size() > 0) {
            forall_res.push_back(z3::forall(loop_args, z3::implies(loop_range, e)));
        } else {
            forall_res.push_back(e);
        }
    }
    for (auto e : initial_res) {
        forall_res.push_back(e);
    }
    return forall_res;
}

z3::expr c2z3::v2z3(Value* v, int dim, int plus) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        return z3ctx.int_val(CI->getSExtValue());
    }
    z3::func_decl f = get_z3_function(v, dim);
    z3::expr_vector args = get_args(dim, false, plus, true);
    return f(args);
}

z3::expr c2z3::use2z3(Use* u) {
    if (u == nullptr) return z3ctx.bool_val(true);
    Value* use_def = u->get();
    Type* tp = use_def->getType();
    const char* var_name = use_def->getName().data();
    bool is_bool = tp->isIntegerTy(1);
    if (auto CI = dyn_cast<ConstantInt>(use_def)) {
        if (is_bool) {
            return z3ctx.bool_val(CI->getSExtValue());
        } else {
            return z3ctx.int_val(CI->getSExtValue());
        }
    }

    LoopInfo& LI = LIs.at(main);
    auto CI = dyn_cast<Instruction>(use_def);
    int dim = LI.getLoopDepth(CI->getParent());
    // z3::sort_vector params(z3ctx);
    // z3::expr_vector args(z3ctx);
    // z3::sort ret_sort = is_bool ? z3ctx.bool_sort() : z3ctx.int_sort();

    // for (int i = 0; i < dim; i++) {
    //     std::string idx = "n" + std::to_string(i);
    //     params.push_back(z3ctx.int_sort());
    //     args.push_back(z3ctx.int_const(idx.data()) + 1);
    // }
    z3::func_decl f = get_z3_function(u);
    z3::expr_vector args = get_args(dim, false, true, false);

    Value* user = u->getUser();
    auto user_inst = dyn_cast<Instruction>(user);
    BasicBlock* user_block = user_inst->getParent();
    BasicBlock* def_block = CI->getParent();
    Loop* user_loop = LI.getLoopFor(user_block);
    Loop* def_loop = LI.getLoopFor(def_block);
    bool is_n = false;
    if (def_loop && def_loop->contains(user_inst)) {
        if (user_loop) {
            if (user_loop->getHeader() == user_block) {
                if (auto phi = dyn_cast_or_null<PHINode>(user)) {
                    BasicBlock* from_block = phi->getIncomingBlock(*u);
                    if (user_loop->isLoopLatch(from_block)) {
                        // is a back edge
                        is_n = true;
                    }
                }
            }
        }
        if (is_n) {
            try {
                if (user_loop) {
                    args.pop_back();
                    std::string idx = "n" + std::to_string(dim - 1);
                    args.push_back(z3ctx.int_const(idx.data()));
                    // args[loop->getLoopDepth() - 1] = args[loop->getLoopDepth() - 1] + 1;
                }
            } catch (...) {

            }
        }
    } else if (def_loop) {
        args.pop_back();
        std::string idx = "N_" + std::to_string(loop2idx[def_loop]) + "_" + std::to_string(dim - 1);
        args.push_back(z3ctx.int_const(idx.data()));
    }
    // z3::func_decl f = z3ctx.function(var_name, params, ret_sort);
    return f(args);
}

std::set<Use*> c2z3::get_bb_conditions(BasicBlock* bb) {
    if (bb_conditions.find(bb) != bb_conditions.end()) {
        return bb_conditions.at(bb);
    }
    std::set<Use*> res;
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(bb);
    for (BasicBlock* prev_bb : predecessors(bb)) {
        if (loop && bb == loop->getHeader() && prev_bb == loop->getLoopLatch()) continue;
        std::set<Use*> prev_uses_set = get_bb_conditions(prev_bb);
        auto path_cond_negated = path_condition_b2b(prev_bb, bb);
        res.insert(path_cond_negated.first);
        res.merge(prev_uses_set);
    }
    bb_conditions.insert_or_assign(bb, res);
    return res;
}

bool c2z3::is_terminal(Value* v) {
    if (isa<Constant>(v)) return true;
    auto inst = dyn_cast_or_null<Instruction>(v);
    assert(inst);
    BasicBlock* bb = inst->getParent();
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(bb);
    if (loop) {
        BasicBlock* header = loop->getHeader();
        return header == bb && isa<PHINode>(v);
    }
    return bb == &main->getEntryBlock() && isa<CallInst>(v);
}


// void c2z3::as_loop_expression(Use* u) {
//     _as_loop_expression(u, z3ctx.bool_val(true));
// }

z3::expr c2z3::loop_expression(Use* u) {
    Value* v = u->get();
    auto inst = dyn_cast_or_null<Instruction>(v);
    if (is_terminal(v)) {
        // return use2z3(u);
        LoopInfo& LI = LIs.at(main);
        int dim = 0;
        if (inst)
            dim = LI.getLoopDepth(inst->getParent());
        return v2z3(v, dim, false);
    }
    assert(inst);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
        Use* op0 = &inst->getOperandUse(0);
        Use* op1 = &inst->getOperandUse(1);
        z3::expr e1 = as_loop_expression(op0);
        z3::expr e2 = as_loop_expression(op1);
        if (opcode == Instruction::And) {
            return e1 && e2;
        } else if (opcode == Instruction::Or) {
            return e1 || e2;
        } else if (opcode == Instruction::Add) {
            return e1 + e2;
        } else if (opcode == Instruction::Sub) {
            return e1 - e2;
        } else if (opcode == Instruction::Mul) {
            return e1 * e2;
        }
    } else if (auto CI = dyn_cast_or_null<ICmpInst>(v)) {
        auto pred = CI->getPredicate();
        Use* op0 = &inst->getOperandUse(0);
        Use* op1 = &inst->getOperandUse(1);
        z3::expr e1 = as_loop_expression(op0);
        z3::expr e2 = as_loop_expression(op1);
        if (pred == ICmpInst::ICMP_EQ) {
            return e1 == e2;
        } else if (pred == ICmpInst::ICMP_NE) {
            return e1 != e2;
        } else if (ICmpInst::isLE(pred)) {
            return e1 <= e2;
        } else if (ICmpInst::isLT(pred)) {
            return e1 < e2;
        } else if (ICmpInst::isGE(pred)) {
            return e1 >= e2;
        } else if (ICmpInst::isGT(pred)) {
            return e1 > e2;
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else if (auto phi = dyn_cast_or_null<PHINode>(v)) {
        assert(phi->getNumIncomingValues() == 1);
        Use* op0 = &phi->getOperandUse(0);
        z3::expr e = loop_expression(op0);
        return e;
    } else {
        throw UnimplementedOperationException(opcode);
    }
}

z3::expr c2z3::as_loop_expression(Use* u) {
    Value* v = u->get();
    auto inst = dyn_cast_or_null<Instruction>(v);
    if (is_terminal(v)) {
        // return use2z3(u);
        LoopInfo& LI = LIs.at(main);
        int dim = 0;
        if (inst)
            dim = LI.getLoopDepth(inst->getParent());
        return v2z3(v, dim, false);
    }
    assert(inst);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
        Use* op0 = &inst->getOperandUse(0);
        Use* op1 = &inst->getOperandUse(1);
        z3::expr e1 = as_loop_expression(op0);
        z3::expr e2 = as_loop_expression(op1);
        if (opcode == Instruction::And || opcode == Instruction::Or) {
            expression2solve.push_back(e1);
            expression2solve.push_back(e2);
            return z3ctx.bool_val(true);
        } else if (opcode == Instruction::Add) {
            return e1 + e2;
        } else if (opcode == Instruction::Sub) {
            return e1 - e2;
        } else if (opcode == Instruction::Mul) {
            return e1 * e2;
        }
    } else if (auto CI = dyn_cast_or_null<ICmpInst>(v)) {
        auto pred = CI->getPredicate();
        Use* op0 = &inst->getOperandUse(0);
        Use* op1 = &inst->getOperandUse(1);
        z3::expr e1 = as_loop_expression(op0);
        z3::expr e2 = as_loop_expression(op1);
        expression2solve.push_back(e1 - e2);
        return z3ctx.bool_val(true);
    } else if (auto phi = dyn_cast_or_null<PHINode>(v)) {
        assert(phi->getNumIncomingValues() == 1);
        Use* op0 = &phi->getOperandUse(0);
        z3::expr e = as_loop_expression(op0);
        return e;
    } else {
        throw UnimplementedOperationException(opcode);
    }

}

z3::expr_vector c2z3::all2z3(Instruction* inst) {
    if (visited_inst.contains(inst)) {
        return z3::expr_vector(z3ctx);
    }
    visited_inst.insert(inst);
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(inst->getParent());
    z3::expr_vector res = inst2z3(inst);
    std::set<Loop*> all_loops;
    for (int i = 0; i < inst->getNumOperands(); i++) {
        Value* cur_v = inst->getOperand(i);
        if (auto CI = dyn_cast<Instruction>(cur_v)) {
            z3::expr_vector cur_vec = all2z3(CI);
            combine_vec(res, cur_vec);
        }
        if (auto phi = dyn_cast<PHINode>(cur_v)) {
            std::set<Use*> uses = get_bb_conditions(phi->getParent());
            for (Use* u : uses) {
                if (u) {
                    z3::expr_vector cur_vec = all2z3(dyn_cast<Instruction>(u->get()));
                    combine_vec(res, cur_vec);
                }
            }
        }
    }
    if (loop && !visited_loops.contains(loop)) {
        visited_loops.insert(loop);
        pc_type loop_pc = loop_condition(loop);
        // errs() << loop_pc.first.to_string() << "\n";
        res.push_back(loop_pc.first);
    }
    return res;
}

pc_type c2z3::path_condition(BasicBlock* bb) {
    BasicBlock* entry = &main->getEntryBlock();
    return path_condition_from_to(entry, bb);
}

std::pair<Use*, bool> c2z3::path_condition_b2b(BasicBlock* from, BasicBlock* to) {
    Instruction* term = from->getTerminator();
    Use* cond = nullptr;
    bool is_negated = false;
    // z3::expr res = z3ctx.bool_val(true);
    if (auto CI = dyn_cast<BranchInst>(term)) {
        if (CI->isConditional()) {
            cond = &CI->getOperandUse(0);
            is_negated = CI->getSuccessor(1) == to;
        }
    }
    return std::make_pair(cond, is_negated);
}

z3::expr c2z3::get_non_neg_args_cond(int dim) {
    z3::expr_vector args = get_pure_args(dim, false);
    z3::expr res = z3ctx.bool_val(true);
    for (int i = 0; i < args.size(); i++) {
        res = res && args[i] >= 0;
    }
    return res;
}

void c2z3::print_path(path_ty p) {
    for (auto bb : p) {
        errs() << bb->getName() << " ";
    }
    errs() << "\n";
}

validation_type c2z3::check_assert(Use* a, int out_idx) {
    User* user = a->getUser();
    auto CI = dyn_cast_or_null<Instruction>(user);
    std::vector<path_ty> paths = get_paths_from_to(&main->getEntryBlock(), CI->getParent());
    validation_type res = correct;
    for (int i = 0; i < paths.size(); i++) {
        auto p = paths[i];
        // print_path(p);
        z3::solver s(z3ctx);
        s.add(path2z3(p));
        std::string filename = "tmp/tmp" + std::to_string(out_idx) + "_path_"+ std::to_string(i) + ".smt2";
        std::ofstream out(filename);
        s.add(!use2z3(a));
        out << s.to_smt2().data() << "\n";
        out.close();

        auto val_res = s.check();
        switch (val_res) {
            case z3::sat  : res = wrong  ; break;
            case z3::unsat: res = correct; break;
            default       : res = unknown; break;
        }
        if (val_res == z3::sat) {
            res = wrong;
            break;
        } else if (val_res == z3::unsat) {

        } else {
            res = unknown;
            break;
        }
    }
    return res;
}

z3::expr c2z3::path_condition_one_stride(BasicBlock* from, BasicBlock* to) {
    z3::expr res = z3ctx.bool_val(true);
    Instruction* term = from->getTerminator();
    if (auto br = dyn_cast_or_null<BranchInst>(term)) {
        if (br->isConditional()) {
            Use* cond = &br->getOperandUse(0);
            res = use2z3(cond);
            res = to == br->getSuccessor(0) ? res : !res;
        }
    }
    return res;
}

z3::expr_vector c2z3::path2z3(path_ty p) {
    z3::expr_vector axioms(z3ctx);
    BasicBlock* prev_bb = nullptr;
    LoopInfo& LI = LIs.at(main);
    for (BasicBlock* bb : p) {
        if (prev_bb) {
            axioms.push_back(path_condition_one_stride(prev_bb, bb));
        }
        Loop* loop = LI.getLoopFor(bb);
        if (loop) {
            visited_loops.insert(loop);
            for (BasicBlock* loop_bb : loop->getBlocks()) {
                for (Instruction& inst : *loop_bb) {
                    if (loop_bb->getTerminator() == &inst) continue;
                    z3::expr_vector local_exprs = inst2z3(&inst);
                    combine_vec(axioms, local_exprs);
                }
            }
            prev_bb = nullptr;
        } else {
            for (Instruction& inst : *bb) {
                if (bb->getTerminator() == &inst) continue;
                z3::expr_vector local_exprs = inst2z3(&inst, prev_bb);
                combine_vec(axioms, local_exprs);
            }
            prev_bb = bb;
        }
    }
    z3::expr n = z3ctx.int_const("n0");
    z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
    std::vector<rec_ty> closed;
    for (Loop* loop : visited_loops) {
        closed_form_ty res = solve_loop(loop);
        z3::expr bnd = loop_bound(loop);
        axioms.push_back(bnd);
        z3::expr_vector ns(z3ctx);
        z3::expr_vector Ns(z3ctx);
        ns.push_back(z3ctx.int_const("n0"));
        Ns.push_back(z3ctx.int_const(("N_" + std::to_string(loop2idx[loop]) + "_0").data()));
        if (!res.empty()) {
            closed.push_back(res);
            z3::expr ind_var = z3ctx.int_const("n0");
            for (auto r : res) {
                z3::expr k = r.first;
                axioms.push_back(z3::forall(ind_var, z3::implies(ind_var >= 0, k == r.second)));
                axioms.push_back(k.substitute(ns, Ns) == r.second.substitute(ns, Ns));
            }
        }
    }
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    src.push_back(n);
    dst.push_back(free_var);
    z3::expr_vector new_axioms(z3ctx);
    for (auto e : axioms) {
        z3::expr cur_e = e;
        for (rec_ty c : closed) {
            for (auto p : c) {
                z3::func_decl f = p.first.decl();
                z3::expr closed_form = p.second.substitute(src, dst);
                // errs() << f.to_string() << " = " << closed_form.to_string() << "\n";
                z3::func_decl_vector fs(z3ctx);
                fs.push_back(f);
                z3::expr_vector closed_forms(z3ctx);
                closed_forms.push_back(closed_form);
                cur_e = cur_e.substitute(fs, closed_forms);
            }
        }
        new_axioms.push_back(cur_e);
    }
    return new_axioms;
}

closed_form_ty c2z3::solve_loop(Loop* loop) {
    rec_ty recs = loop2rec(loop);
    z3::expr_vector res(z3ctx);
    // for (auto r : recs) {
    //     errs() << r.first.to_string() << " = " << r.second.to_string() << "\n";
    // }
    initial_ty initials = loop2initial(loop);
    auto rec_s = rec_solver(z3ctx);
    rec_s.set_eqs(recs);
    rec_s.add_initial_values(initials.first, initials.second);
    rec_s.solve();
    // z3::expr bnd = loop_bound(loop);
    // res.push_back(bnd);
    // z3::expr_vector ns(z3ctx);
    // z3::expr_vector Ns(z3ctx);
    // ns.push_back(z3ctx.int_const("n0"));
    // Ns.push_back(z3ctx.int_const(("N_" + std::to_string(loop2idx[loop]) + "_0").data()));
    closed_form_ty rec_res = rec_s.get_res();
    closed_form_ty new_rec_res = rec_res;
    int dim = loop->getLoopDepth();
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    z3::expr n = z3ctx.int_const("n0");
    z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
    src.push_back(n);
    dst.push_back(free_var);
    for (auto bb : loop->getBlocks()) {
        for (auto& inst : *bb) {
            if (inst.hasName()) {
                z3::expr cur_e = express_v_as_header_phis(&inst);
                for (auto p : rec_res) {
                    z3::func_decl f = p.first.decl();
                    z3::expr closed_form = p.second.substitute(src, dst);
                    // // errs() << f.to_string() << " = " << closed_form.to_string() << "\n";
                    z3::func_decl_vector fs(z3ctx);
                    fs.push_back(f);
                    z3::expr_vector closed_forms(z3ctx);
                    closed_forms.push_back(closed_form);
                    cur_e = cur_e.substitute(fs, closed_forms);
                }
                z3::func_decl cur_f = get_z3_function(&inst, dim);
                z3::expr_vector args = get_args(dim, false, false, false, loop);
                new_rec_res.insert_or_assign(cur_f(args), cur_e);
            }
        }
    }
    // if (!rec_res.empty()) {
    //     // closed.push_back(res);
    //     z3::expr ind_var = z3ctx.int_const("n0");
    //     for (auto r : rec_res) {
    //         z3::expr k = r.first;
    //         res.push_back(z3::forall(ind_var, z3::implies(ind_var >= 0, k == r.second)));
    //         res.push_back(k.substitute(ns, Ns) == r.second.substitute(ns, Ns));
    //         // errs() << (k.substitute(ns, Ns) == r.second.substitute(ns, Ns)).to_string() << "\n";
    //     }
    // }
    return new_rec_res;
}

validation_type c2z3::check_assert_backward(Use* a, int out_idx) {
    visited_loops.clear();
    visited_inst.clear();

    z3::solver s(z3ctx);

    // as_loop_expression(a);
    // for (auto e : expression2solve) {
    //     errs() << e.to_string() << "\n";
    // }

    User* user = a->getUser();
    int dim = 0;
    if (!isa<Constant>(user)) {
        auto CI = dyn_cast_or_null<Instruction>(user);
        LoopInfo& LI = LIs.at(main);
        dim = LI.getLoopDepth(CI->getParent());
    }
    z3::expr_vector args = get_pure_args(dim, false);
    z3::expr non_neg_args_cond = get_non_neg_args_cond(dim);

    if (args.size() > 0) {
        s.add(!z3::forall(args, z3::implies(non_neg_args_cond, use2z3(a))));
    } else {
        s.add(!use2z3(a));
    }

    Value* v = a->get();
    if (auto inst = dyn_cast_or_null<Instruction>(v)) {
        s.add(all2z3(inst));
        pc_type assert_pc = path_condition(inst->getParent());
        s.add(assert_pc.first);
        for (Use* u : assert_pc.second) {
            Value* use_v = u->get();
            auto inst_use = dyn_cast_or_null<Instruction>(use_v);
            if (inst_use) s.add(all2z3(inst_use));
        }
    }
    std::vector<rec_ty> closed;
    for (Loop* loop : visited_loops) {
        rec_ty recs = loop2rec(loop);
        // for (auto r : recs) {
        //     errs() << r.first.to_string() << " = " << r.second.to_string() << "\n";
        // }
        initial_ty initials = loop2initial(loop);
        auto rec_s = rec_solver(z3ctx);
        rec_s.set_eqs(recs);
        rec_s.add_initial_values(initials.first, initials.second);
        rec_s.solve();
        z3::expr bnd = loop_bound(loop);
        s.add(bnd);
        z3::expr_vector ns(z3ctx);
        z3::expr_vector Ns(z3ctx);
        ns.push_back(z3ctx.int_const("n0"));
        Ns.push_back(z3ctx.int_const(("N_" + std::to_string(loop2idx[loop]) + "_0").data()));
        rec_ty res = rec_s.get_res();
        if (!res.empty()) {
            closed.push_back(res);
            z3::expr ind_var = z3ctx.int_const("n0");
            for (auto r : res) {
                z3::expr k = r.first;
                s.add(z3::forall(ind_var, z3::implies(ind_var >= 0, k == r.second)));
                s.add(k.substitute(ns, Ns) == r.second.substitute(ns, Ns));
                // errs() << (k.substitute(ns, Ns) == r.second.substitute(ns, Ns)).to_string() << "\n";
            }
        }
    }
    z3::expr_vector axioms = s.assertions();
    z3::expr_vector new_axioms(z3ctx);
    z3::expr n = z3ctx.int_const("n0");
    z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    src.push_back(n);
    dst.push_back(free_var);
    for (auto e : axioms) {
        z3::expr cur_e = e;
        for (rec_ty c : closed) {
            for (auto p : c) {
                z3::func_decl f = p.first.decl();
                z3::expr closed_form = p.second.substitute(src, dst);
                // errs() << f.to_string() << " = " << closed_form.to_string() << "\n";
                z3::func_decl_vector fs(z3ctx);
                fs.push_back(f);
                z3::expr_vector closed_forms(z3ctx);
                closed_forms.push_back(closed_form);
                cur_e = cur_e.substitute(fs, closed_forms);
            }
        }
        new_axioms.push_back(cur_e);
    }
    s.reset();
    s.add(new_axioms);
    std::string filename = "tmp/tmp" + std::to_string(out_idx) + ".smt2";
    std::ofstream out(filename);
    out << s.to_smt2().data() << "\n";
    out.close();
    auto val_res = s.check();
    validation_type res = unknown;
    switch (val_res) {
        case z3::sat  : res = wrong  ; break;
        case z3::unsat: res = correct; break;
        default       : res = unknown; break;
    }
    return res;
}

std::vector<path_ty> c2z3::get_paths_from_to(BasicBlock* from, BasicBlock* to) {
    std::vector<path_ty> res;
    LoopInfo& LI = LIs.at(main);
    if (from == to) {
        res.push_back({from});
    }
    for (auto bb = pred_begin(to); bb != pred_end(to); bb++) {
        BasicBlock* cur_bb = *bb;
        if (is_back_edge(cur_bb, to)) continue;
        Loop *loop = LI.getLoopFor(cur_bb);
        if (loop) cur_bb =loop->getHeader();
        auto prev_paths = get_paths_from_to(from, cur_bb);
        for (auto p : prev_paths) {
            p.push_back(to);
            res.push_back(p);
        }
    }
    return res;
}

z3::func_decl c2z3::get_z3_function(Use* u) {
    Value* v = u->get();
    auto inst = dyn_cast_or_null<Instruction>(v);
    // assert(inst);
    LoopInfo& LI = LIs.at(main);
    int dim = LI.getLoopDepth(inst->getParent());
    return get_z3_function(v, dim);
    // z3::sort_vector args_sorts(z3ctx);
    // z3::sort ret_sort = z3ctx.int_sort();
    // for (int i = 0; i < dim; i++) {
    //     args_sorts.push_back(z3ctx.int_sort());
    // }
    // const char* var_name = v->getName().data();
    // return z3ctx.function(var_name, args_sorts, ret_sort);
}

bool c2z3::is_bool(Value* v) {
    Type* ty = v->getType();
    return ty->isIntegerTy() && ty->getIntegerBitWidth() == 1;
}

z3::func_decl c2z3::get_z3_function(Value* v, int dim) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    assert(inst);
    z3::sort_vector args_sorts(z3ctx);
    z3::sort ret_sort = is_bool(v) ? z3ctx.bool_sort() : z3ctx.int_sort();
    int arity = 0;
    if (auto load = dyn_cast_or_null<LoadInst>(v)) {
        Value* ptr = load->getPointerOperand();
        auto get_ptr_inst = dyn_cast_or_null<GetElementPtrInst>(ptr);
        assert(get_ptr_inst);
        // get_ptr_inst->get
    }
    for (int i = 0; i < dim + arity; i++) {
        args_sorts.push_back(z3ctx.int_sort());
    }
    const char* var_name = v->getName().data();
    return z3ctx.function(var_name, args_sorts, ret_sort);
}


z3::expr_vector c2z3::get_args(int dim, bool c, bool plus, bool prefix, Loop* loop) {
    z3::expr_vector args(z3ctx);
    // const char* idx_prefix = c ? "N" : "n";
    std::string idx_prefix = "n";
    if (c) {
        idx_prefix = "N_" + std::to_string(loop2idx[loop]) + "_";
    }
    for (int i = 0; i < dim; i++) {
        std::string n_name = idx_prefix + std::to_string(i);
        if (plus) {
            if (prefix) {
                args.push_back(1 + z3ctx.int_const(n_name.data()));
            } else {
                args.push_back(z3ctx.int_const(n_name.data()) + 1);
            }
            // args.push_back(z3ctx.int_const(n_name.data()) + 1);
        } else {
            args.push_back(z3ctx.int_const(n_name.data()));
        }
    }
    return args;
}

pc_type c2z3::loop_condition(Loop* loop) {
    BasicBlock* header = loop->getHeader();
    BasicBlock* latch = loop->getLoopLatch();
    Instruction* term = loop->getLoopLatch()->getTerminator();
    bool is_negated = false;
    Use* cond = nullptr;
    if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
        if (CI->isConditional()) {
            is_negated = CI->getSuccessor(1) == header;
            cond = &CI->getOperandUse(0);
        }
    }
    z3::expr piece = use2z3(cond);
    // z3::func_decl cond_func = get_z3_function(cond);
    // z3::expr_vector loop_args = get_args(cond_func.arity());
    // z3::expr piece = cond_func(loop_args);

    pc_type local_pc = path_condition_from_to(header, latch);
    piece = is_negated ? !piece : piece;
    piece = piece && local_pc.first;
    LoopInfo& LI = LIs.at(main);
    int dim = LI.getLoopDepth(header);
    z3::expr_vector ns(z3ctx);
    z3::expr_vector n1s(z3ctx);
    z3::expr_vector Ns(z3ctx);
    z3::expr premises = z3ctx.bool_val(true);
    z3::expr cons_N = z3ctx.bool_val(true);
    for (int i = 0; i < dim; i++) {
        std::string idx = "n" + std::to_string(i);
        ns.push_back(z3ctx.int_const(idx.data()));
        n1s.push_back(1 + z3ctx.int_const(idx.data()));
        idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(i);
        Ns.push_back(z3ctx.int_const(idx.data()));
        premises = premises && ns.back() < Ns.back();
        cons_N = cons_N && Ns.back() >= 0;
    }
    piece = piece.substitute(n1s, ns);
    z3::expr loop_cond = z3::forall(ns, z3::implies(premises, piece));
    z3::expr exit_cond = !piece.substitute(ns, Ns);
    z3::expr res = loop_cond && cons_N && exit_cond;
    // z3::expr res = cons_N && exit_cond;
    // res = res && loop_cond && exit_cond;
    // res = res && local_pc.first;
    local_pc.second.insert(cond);
    // return res;
    return {res, local_pc.second};
}

z3::expr c2z3::path_condition_header2bb(BasicBlock* bb) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(bb);
    BasicBlock* header = &main->getEntryBlock();
    if (loop) header = loop->getHeader();
    for (BasicBlock* prev_bb : predecessors(bb)) {
        Loop* prev_loop = LI.getLoopFor(prev_bb);
        z3::expr prev_cond = path_condition_header2bb(bb);
        if (prev_loop == loop) {
        }
    }
}

z3::expr c2z3::simple_path_condition_from_to(BasicBlock* from, BasicBlock* to) {
    DominatorTree& DT = DTs.at(main);
    assert(DT.dominates(from, to));
    z3::expr res = z3ctx.bool_val(false);
    if (from == to) return z3ctx.bool_val(true);
    LoopInfo& LI = LIs.at(main);
    Loop* to_loop = LI.getLoopFor(to);
    for (BasicBlock* prev_bb : predecessors(to)) {
        Loop* prev_loop = LI.getLoopFor(prev_bb);
        z3::expr cur_cond = simple_path_condition_from_to(from, prev_bb);
        Instruction* term = prev_bb->getTerminator();
        if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
            if (CI->isConditional()) {
                Use* u = &CI->getOperandUse(0);
                z3::expr local_cond = use2z3(u);
                local_cond = CI->getSuccessor(0) == to? local_cond : !local_cond;
                cur_cond = cur_cond && local_cond;
            }
        }
        res = res || cur_cond;
    }
    return res;
}

z3::expr c2z3::loop_bound(Loop* loop) {
    BasicBlock* header = loop->getHeader();
    BasicBlock* latch = loop->getLoopLatch();
    Instruction* term = latch->getTerminator();
    bool is_negated = false;
    Use* cond = nullptr;
    if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
        if (CI->isConditional()) {
            is_negated = CI->getSuccessor(1) == header;
            cond = &CI->getOperandUse(0);
        }
    }
    z3::expr piece = use2z3(cond);
    // if (cond) {
    //     z3::expr cond_as_phis = express_v_as_header_phis(cond->get());
    //     errs() << cond_as_phis.to_string() << "\n";
    // }
    // z3::func_decl cond_func = get_z3_function(cond);
    // z3::expr_vector loop_args = get_args(cond_func.arity());
    // z3::expr piece = cond_func(loop_args);

    pc_type local_pc = path_condition_from_to(header, latch);
    // errs() << local_pc.first.to_string() << "\n";
    std::set<Use*> all_used = local_pc.second;
    std::set<PHINode*> all_phis;
    if (cond) all_used.insert(cond);

    rec_ty loop_recs = loop2rec(loop);
    initial_ty loop_initials = loop2initial(loop);
    auto rec_s = rec_solver(z3ctx);
    rec_s.set_eqs(loop_recs);
    rec_s.add_initial_values(loop_initials.first, loop_initials.second);

    piece = is_negated ? !piece : piece;
    piece = piece && local_pc.first;
    LoopInfo& LI = LIs.at(main);
    int dim = LI.getLoopDepth(header);
    z3::expr_vector ns(z3ctx);
    z3::expr_vector n1s(z3ctx);
    z3::expr_vector Ns(z3ctx);
    z3::expr premises = z3ctx.bool_val(true);
    z3::expr cons_N = z3ctx.bool_val(true);
    for (int i = 0; i < dim; i++) {
        std::string idx = "n" + std::to_string(i);
        ns.push_back(z3ctx.int_const(idx.data()));
        n1s.push_back(1 + z3ctx.int_const(idx.data()));
        idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(i);
        Ns.push_back(z3ctx.int_const(idx.data()));
        premises = premises && ns.back() < Ns.back() && ns.back() >= 0;
        cons_N = cons_N && Ns.back() >= 0;
    }
    piece = piece.substitute(n1s, ns);

    for (Use* u : all_used) {
        z3::expr loop_expr = loop_expression(u);
        z3::expr_vector src(z3ctx);
        z3::expr_vector dst(z3ctx);
        src.push_back(v2z3(u->get(), dim, false));
        dst.push_back(loop_expr);
        // loop_cond = loop_cond.substitute(src, dst);
        piece = piece.substitute(src, dst);
        std::set<PHINode*> local_phis = get_header_defs(u->get());
        all_phis.insert(local_phis.begin(), local_phis.end());
    }
    // for (auto phi : all_phis) {
    //     initial_ty initial = header_phi_as_initial(phi);
    //     // z3::expr to_solved = v2z3(phi, dim, false);
    //     // errs() << to_solved.to_string() << "\n";
    //     rec_s.add_initial_values(initial.first, initial.second);
    // }
    rec_s.solve();
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    closed_form_ty closed = rec_s.get_res();
    for (auto r : closed) {
        src.push_back(r.first);
        dst.push_back(r.second);
        // errs() << r.first.to_string() << " = " << r.second.to_string() << "\n";
    }
    piece = piece.substitute(src, dst);
    // errs() << piece.to_string() << "\n";
    // errs() << piece.to_string() << "\n";
    z3::expr loop_cond = z3::forall(ns, z3::implies(premises, piece));
    z3::expr exit_cond = !piece.substitute(ns, Ns);
    z3::expr res = loop_cond && cons_N && exit_cond;
    // errs() << res.to_string() << "\n";
    z3::tactic t = z3::tactic(z3ctx, "qe"); // & z3::tactic(z3ctx, "ctx-solver-simplify");
    z3::goal g(z3ctx);
    g.add(res);
    auto r = t.apply(g);
    z3::expr final_res = z3ctx.bool_val(true);
    for (int i = 0; i < r.size(); i++) {
        final_res = final_res && r[i].as_expr();
        // errs() << r[i].as_expr().to_string() << "\n";
    }
    // errs() << exit_cond.to_string() << "\n";
    // z3::expr res = cons_N && exit_cond;
    // res = res && loop_cond && exit_cond;
    // res = res && local_pc.first;
    // return res;
    return final_res;
}

pc_type c2z3::path_condition_from_to(BasicBlock* from, BasicBlock* to) {
    if (from == to) return {z3ctx.bool_val(true), {}};
    pc_type res = {z3ctx.bool_val(false), {}};
    LoopInfo& LI = LIs.at(main);
    Loop* from_loop = LI.getLoopFor(from);
    Loop* to_loop = LI.getLoopFor(to);
    for (BasicBlock* bb : predecessors(to)) {
        BasicBlock* prev_bb = bb;
        if (!is_back_edge(prev_bb, to)) {
            if (from_loop && !from_loop->contains(to)) {
                prev_bb = from_loop->getHeader();
            }
            auto pc = path_condition_from_to(from, prev_bb);
            pc_type local_pc = path_condition_from_to_straight(prev_bb, to);
            pc_type total_pc = pc_and(pc, local_pc);
            res = pc_or(res, total_pc);
        }
    }
    res.first = res.first.simplify();
    z3::tactic t = z3::tactic(z3ctx, "tseitin-cnf") & z3::tactic(z3ctx, "ctx-solver-simplify");
    z3::goal g(z3ctx);
    g.add(res.first);
    auto qq = t.apply(g);
    res.first = z3ctx.bool_val(true);
    for (int i = 0; i < qq.size(); i++) {
        // errs() << qq[i].as_expr().to_string() << "\n";
        res.first = res.first && qq[i].as_expr();
    }
    return res;
}

pc_type c2z3::pc_and(const pc_type& a, const pc_type& b) {
    z3::expr cond = a.first && b.first;
    std::set<Use*> use_set;
    std::set_union(a.second.begin(), a.second.end(),
                   b.second.begin(), b.second.end(),
                   std::inserter(use_set, use_set.end()));
    return {cond, use_set};
}

pc_type c2z3::pc_or(const pc_type& a, const pc_type& b) {
    z3::expr cond = a.first || b.first;
    std::set<Use*> use_set;
    std::set_union(a.second.begin(), a.second.end(),
                   b.second.begin(), b.second.end(),
                   std::inserter(use_set, use_set.end()));
    return {cond, use_set};
}

bool c2z3::is_back_edge(BasicBlock* from, BasicBlock* to) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(from);
    bool res = loop && loop->isLoopLatch(from) && loop->getHeader() == to;
    return res;
}


pc_type c2z3::path_condition_from_to_straight(BasicBlock* from, BasicBlock* to) {
    pc_type res = {z3ctx.bool_val(true), {}};
    PostDominatorTree& PDT = PDTs.at(main);
    if (PDT.dominates(to, from)) return res;
    Instruction* term = from->getTerminator();
    LoopInfo& LI = LIs.at(main);
    Loop* from_loop = LI.getLoopFor(from);
    Loop* to_loop = LI.getLoopFor(to);
    if (from_loop) {
        SmallVector<BasicBlock*, 10> exit_blocks;
        from_loop->getExitBlocks(exit_blocks);
        if (std::find(exit_blocks.begin(), exit_blocks.end(), to) != exit_blocks.end()) {
            return res;
        }
    }
    if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
        if (CI->isConditional()) {
            Use& u = CI->getOperandUse(0);
            res.first = use2z3(&u);
            res.second.insert(&u);
            res.first = CI->getSuccessor(0) == to ? res.first : !res.first;
        }
    }
    res.first = res.first.simplify();
    return res;
}


void c2z3::get_loop_idx() {
    LoopInfo& LI = LIs.at(main);
    int i = 1;
    for (Loop* loop : LI.getLoopsInPreorder()) {
        loop2idx.insert_or_assign(loop, i++);
    }
}