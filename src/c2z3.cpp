#include "c2z3.h"
#include <stdexcept>
#include <algorithm>
#include <iterator>
#include <numeric>

class UnimplementedOperationException: public std::runtime_error {
    public:
        UnimplementedOperationException(int opcode): runtime_error(Instruction::getOpcodeName(opcode)) {}
        UnimplementedOperationException(const char* err): runtime_error(err) {}
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

z3::expr_vector merge_vec(z3::expr_vector& v1, z3::expr_vector& v2) {
    z3::expr_vector res(v1.ctx());
    combine_vec(res, v1);
    combine_vec(res, v2);
    return res;
}

c2z3::c2z3(std::unique_ptr<Module> &mod): m(std::move(mod)), rec_s(z3ctx), expression2solve(z3ctx) {
    // Register all the basic analyses with the managers.
    for (auto F = m->begin(); F != m->end(); F++) {
        if (!F->getName().starts_with("__VERIFIER") && F->getName() != "main") {
            if (F->hasFnAttribute(Attribute::NoInline)) {
                F->removeFnAttr(Attribute::NoInline);
            }
        }
        if (F->getName().starts_with("__VERIFIER_nondet")) {
            unknown_fn = &*F;
        }
    }
    // PB.registerModuleAnalyses(MAM);
    // PB.registerCGSCCAnalyses(CGAM);
    // PB.registerFunctionAnalyses(FAM);
    // PB.registerLoopAnalyses(LAM);
    // PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    std::error_code ec;
    raw_fd_ostream output_fd("tmp/tmp.ll", ec);

    raw_fd_ostream before_fd("tmp/before.ll", ec);
    m->print(before_fd, NULL);
    before_fd.close();

    ModulePassManager MPM_pre;
    analyze_module_pre(MPM_pre);

    // LoopInfo& LI = LIs.at(main);
    // auto all_loops = LI.getLoopsInPreorder();
    // for (Loop* loop : all_loops) {
    //     if (loop->getLoopDepth() == 1) {
    //         BasicBlock* header = loop->getHeader();
    //         BasicBlock* latch = loop->getLoopLatch();
    //         std::vector<path_ty> paths = get_paths_from_to_loop(loop);
    //         for (auto p : paths) {
    //             print_path(p);
    //         }
    //     }
    // }

    // loop_transformer transformer(main, LI, unknown_fn);
    // transformer.transform_function();

    // raw_fd_ostream after_fd("tmp/after.ll", ec);
    // m->print(after_fd, NULL);

    // ModulePassManager MPM_post;
    // analyze_module_post(MPM_post);

    m->print(output_fd, NULL);
    output_fd.close();
}

int c2z3::get_successor_index(BranchInst* br, const BasicBlock* bb) {
    int res = -1;
    for (int i = 0; i < br->getNumSuccessors(); i++) {
        if (br->getSuccessor(i) == bb) {
            return i;
        }
    }
    return res;
}

void c2z3::clear_all_info() {
    LIs.clear();
    DTs.clear();
    PDTs.clear();
    MSSAs.clear();
    // LAM = LoopAnalysisManager();
    // FAM = FunctionAnalysisManager();
    // CGAM = CGSCCAnalysisManager();
    // MAM = ModuleAnalysisManager();
    // MAM.clear();
    // CGAM.clear();
    // FAM.clear();
    // LAM.clear();
}

void c2z3::analyze_module_post(ModulePassManager& MPM) {
    clear_all_info();
    LAM = LoopAnalysisManager();
    FAM = FunctionAnalysisManager();
    CGAM = CGSCCAnalysisManager();
    MAM = ModuleAnalysisManager();
    PB = PassBuilder();
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    // std::error_code ec;
    // raw_fd_ostream output_fd("tmp/tmp.ll", ec);

    MPM.addPass(ModuleInlinerPass());
    MPM.addPass(createModuleToFunctionPassAdaptor(PromotePass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(SROAPass(SROAOptions::ModifyCFG)));
    MPM.addPass(createModuleToFunctionPassAdaptor(LCSSAPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(SimplifyCFGPass()));

    // MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(LoopRotatePass())));
    MPM.addPass(createModuleToFunctionPassAdaptor(LoopSimplifyPass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(LoopFusePass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(IndVarSimplifyPass())));
    MPM.addPass(createModuleToFunctionPassAdaptor(SCCPPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(GVNPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(InstructionNamerPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(AggressiveInstCombinePass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(MemorySSAPrinterPass(output_fd)));
    // MPM.addPass(createModuleToFunctionPassAdaptor(MemorySSAWrapperPass()));

    MPM.run(*m, MAM);
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
}

void c2z3::analyze_module_pre(ModulePassManager& MPM) {
    clear_all_info();
    LAM = LoopAnalysisManager();
    FAM = FunctionAnalysisManager();
    CGAM = CGSCCAnalysisManager();
    MAM = ModuleAnalysisManager();
    PB = PassBuilder();
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    // std::error_code ec;
    // raw_fd_ostream output_fd("tmp/tmp.ll", ec);

    MPM.addPass(ModuleInlinerPass());
    MPM.addPass(createModuleToFunctionPassAdaptor(PromotePass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(SROAPass(SROAOptions::ModifyCFG)));
    MPM.addPass(createModuleToFunctionPassAdaptor(LoopSimplifyPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(LCSSAPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(SimplifyCFGPass()));

    // MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(LoopRotatePass())));
    // MPM.addPass(createModuleToFunctionPassAdaptor(LoopFusePass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(createFunctionToLoopPassAdaptor(IndVarSimplifyPass())));
    MPM.addPass(createModuleToFunctionPassAdaptor(SCCPPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(GVNPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(DCEPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(InstructionNamerPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(AggressiveInstCombinePass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(RegToMemPass()));
    // MPM.addPass(createModuleToFunctionPassAdaptor(MemorySSAPrinterPass(output_fd)));
    // MPM.addPass(createModuleToFunctionPassAdaptor(MemorySSAWrapperPass()));

    MPM.run(*m, MAM);
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
}

std::vector<PHINode*> c2z3::get_all_phi_nodes(Function* f) {
    std::vector<PHINode*> phis;
    for (BasicBlock& bb : *f) {
        for (Instruction& inst : bb) {
            if (auto phi = dyn_cast_or_null<PHINode>(&inst)) {
                phis.push_back(phi);
            }
        }
    }
    return phis;
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
    if (!inst) return {};
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
    // z3::expr rec_def = v2z3(phi, loop->getLoopDepth(), true);
    z3::expr rec_def = v2z3(phi);
    rec_ty res;
    res.insert_or_assign(rec_def, rec_z3);
    return res;
}

initial_ty c2z3::header_phi_as_initial(PHINode* phi) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(phi->getParent());
    // int dim = loop->getLoopDepth();
    z3::func_decl f = get_z3_function(phi);
    z3::expr_vector args = get_args(0);
    // args.pop_back();
    // args.push_back(z3ctx.int_val(0));
    rec_ty res;
    BasicBlock* initial_bb = phi->getIncomingBlock(0);
    if (initial_bb == loop->getLoopLatch()) initial_bb = phi->getIncomingBlock(1);
    int dim_initial = LI.getLoopDepth(initial_bb);
    int operand_idx = phi->getBasicBlockIndex(initial_bb);
    // z3::expr initial_v = v2z3(phi->getIncomingValueForBlock(initial_bb), dim_initial, false);
    z3::expr initial_v = v2z3(phi->getOperand(operand_idx));
    // res.insert_or_assign(f(args), initial_v);
    z3::expr_vector fs(z3ctx);
    z3::expr_vector vs(z3ctx);
    fs.push_back(f(args));
    vs.push_back(initial_v);
    return {fs, vs};
}

z3::expr c2z3::express_v_as_header_phis(Value* v) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        int svalue = CI->getSExtValue();
        return is_bool(v) ? z3ctx.bool_val(svalue) : z3ctx.int_val(svalue);
    }
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(inst->getParent());
    return _express_v_as_header_phis(v, loop);
}

z3::expr c2z3::_express_v_as_header_phis(Value* v, Loop* target_loop) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        int svalue = CI->getSExtValue();
        return is_bool(v) ? z3ctx.bool_val(svalue) : z3ctx.int_val(svalue);
    }
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    BasicBlock* bb = inst->getParent();
    Loop* loop = LI.getLoopFor(bb);
    int dim = LI.getLoopDepth(bb);
    if (loop != target_loop) {
        return v2z3(v);
        // return v2z3(v, dim, false);
    }
    if (bb == loop->getHeader() && isa<PHINode>(v)) {
        return v2z3(v);
        // return v2z3(v, dim, false);
    }
    z3::func_decl f = get_z3_function(v);
    z3::expr_vector args = get_args(0, false, false, false);
    z3::expr_vector res(z3ctx);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = _express_v_as_header_phis(op0, target_loop);
        z3::expr z3op1 = _express_v_as_header_phis(op1, target_loop);
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
        z3::expr z3op0 = _express_v_as_header_phis(op0, target_loop);
        z3::expr z3op1 = _express_v_as_header_phis(op1, target_loop);
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
        z3::expr cond = _express_v_as_header_phis(CI->getOperand(0), target_loop);
        z3::expr first = _express_v_as_header_phis(CI->getOperand(1), target_loop);
        z3::expr second = _express_v_as_header_phis(CI->getOperand(2), target_loop);
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
    } else if (auto CI = dyn_cast_or_null<SExtInst>(inst)) {
        return _express_v_as_header_phis(CI->getOperand(0), target_loop);
    } else if (auto CI = dyn_cast_or_null<ZExtInst>(inst)) {
        return _express_v_as_header_phis(CI->getOperand(0), target_loop);
    } else if (auto CI = dyn_cast_or_null<LoadInst>(inst)) {
        z3::func_decl arr_f = get_array_function(inst);
        array_access_ty access = get_array_access_from_load_store(CI);
        z3::expr_vector indices(z3ctx);
        for (auto u : access.second) {
            Value* v = u->get();
            indices.push_back(_express_v_as_header_phis(v, target_loop));
        }
        z3::expr_vector arr_n_args = merge_vec(indices, args);
        return arr_f(arr_n_args);
    } else {
        throw UnimplementedOperationException(opcode);
    }
    // z3::expr final_res = z3ctx.bool_val(true);
    // for (auto e : res) {
    //     final_res = final_res && e;
    // }
    // return final_res;
}

BasicBlock* c2z3::find_nearest_common_dominator_phi(DominatorTree& DT, PHINode* phi) {
    BasicBlock* branch_bb = phi->getIncomingBlock(0);
    for (int i = 1; i < phi->getNumIncomingValues(); i++) {
        BasicBlock* cur_bb = phi->getIncomingBlock(i);
        branch_bb = DT.findNearestCommonDominator(branch_bb, cur_bb);
    }
    return branch_bb;
}

z3::expr c2z3::phi2ite_header(PHINode* phi) {
    if (phi->getNumIncomingValues() == 1) {
        return express_v_as_header_phis(phi->getIncomingValue(0));
    }
    DominatorTree& DT = DTs.at(main);
    PostDominatorTree& PDT = PDTs.at(main);
    assert(phi->getNumIncomingValues() >= 2);
    BasicBlock* bb0 = phi->getIncomingBlock(0);
    BasicBlock* bb1 = phi->getIncomingBlock(1);
    BasicBlock* branch_bb = find_nearest_common_dominator_phi(DT, phi); // DT.findNearestCommonDominator(bb0, bb1);
    BasicBlock* phi_bb = phi->getParent();
    LoopInfo& LI = LIs.at(main);
    if (PDT.dominates(phi_bb, branch_bb)) {
        z3::expr res = express_v_as_header_phis(*(phi->incoming_values().end() - 1));
        for (int i = phi->getNumIncomingValues() - 2; i >= 0; i--) {
            BasicBlock* incoming_bb = phi->getIncomingBlock(i);
            z3::expr path_cond_merge2incoming = phi2ite_find_path_condition(branch_bb, incoming_bb);
            z3::expr path_cond_incoming2merge = phi2ite_find_path_condition_one_step(incoming_bb, phi_bb);
            z3::expr cur_cond = path_cond_merge2incoming && path_cond_incoming2merge;
            Value* cur_v = phi->getIncomingValue(i);
            z3::expr cur_v2z3 = express_v_as_header_phis(cur_v);
            res = z3::ite(cur_cond, cur_v2z3, res);
        }
        return res;
    }
    // int dim = LI.getLoopDepth(curB);
    // if (PDT.dominates(curB, merge_bb)) {
    //     const Instruction* term = merge_bb->getTerminator();
    //     const BranchInst* branch = dyn_cast<BranchInst>(term);
    //     if (branch && branch->isConditional()) {
    //         Value* condV = branch->getCondition();
    //         const BasicBlock* true_b = bb0;
    //         const BasicBlock* false_b = bb1;
    //         if (DT.dominates(branch->getSuccessor(0), bb0) || DT.dominates(branch->getSuccessor(1), bb1)) {
    //             true_b = bb0;
    //             false_b = bb1;
    //         } else {
    //             true_b = bb1;
    //             false_b = bb0;
    //         }
    //         int true_idx = phi->getBasicBlockIndex(true_b);
    //         int false_idx = phi->getBasicBlockIndex(false_b);
    //         // z3::expr cond = v2z3(condV, dim, false);
    //         z3::expr cond = express_v_as_header_phis(condV);
    //         z3::expr v0 = express_v_as_header_phis(phi->getIncomingValue(true_idx));
    //         z3::expr v1 = express_v_as_header_phis(phi->getIncomingValue(false_idx));
    //         // z3::expr v0 = v2z3(phi->getIncomingValue(true_idx), dim, false);
    //         // z3::expr v1 = v2z3(phi->getIncomingValue(false_idx), dim, false);
    //         return z3::ite(cond, v0, v1);
    //         // Value* new_select = builder.CreateSelect(condV, phi->getIncomingValue(true_idx), phi->getIncomingValue(false_idx));
    //         // new_select->setName(v->getName());
    //         // inst = dyn_cast<Instruction>(new_select);
    //     }
    // }
    return z3ctx.bool_val(false);
}

z3::expr c2z3::phi2ite_find_path_condition(BasicBlock* from, BasicBlock* to) {
    if (from == to) return z3ctx.bool_val(true);
    z3::expr res = z3ctx.bool_val(false);
    LoopInfo& LI = LIs.at(main);
    Loop* from_loop = LI.getLoopFor(from);
    Loop* to_loop = LI.getLoopFor(to);
    for (BasicBlock* bb : predecessors(to)) {
        BasicBlock* prev_bb = bb;
        if (!is_back_edge(prev_bb, to)) {
            if (from_loop && !from_loop->contains(to)) {
                prev_bb = from_loop->getHeader();
            }
            z3::expr pc = phi2ite_find_path_condition(from, prev_bb);
            z3::expr local_pc = phi2ite_find_path_condition_one_step(prev_bb, to);
            z3::expr total_pc = pc && local_pc;
            res = res || total_pc;
            res = res || total_pc;
        }
    }
    res = res.simplify();
    z3::tactic t = z3::tactic(z3ctx, "tseitin-cnf") & z3::tactic(z3ctx, "ctx-solver-simplify");
    z3::goal g(z3ctx);
    g.add(res);
    auto qq = t.apply(g);
    res = z3ctx.bool_val(true);
    for (int i = 0; i < qq.size(); i++) {
        res = res && qq[i].as_expr();
    }
    return res;
}

z3::expr c2z3::phi2ite_find_path_condition_one_step(BasicBlock* from, BasicBlock* to) {
    z3::expr res = z3ctx.bool_val(true);
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
            Value* v = CI->getOperand(0);
            // res.first = use2z3(&u);
            res = express_v_as_header_phis(v);
            res = CI->getSuccessor(0) == to ? res : !res;
        }
    }
    res = res.simplify();
    return res;
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
    if (loop->isInnermost()) {
        for (auto& phi : header->phis()) {
            rec_ty phi_rec = header_phi_as_rec(&phi);
            total_recs.insert(phi_rec.begin(), phi_rec.end());
        }
        return total_recs;
    } else {
        // auto paths = get_paths_from_to_loop(loop);
        for (auto& phi : header->phis()) {
            rec_ty phi_rec = header_phi_as_rec_nested(&phi);
            total_recs.insert(phi_rec.begin(), phi_rec.end());
        }
        return total_recs;
    }
}

rec_ty
c2z3::header_phi_as_rec_nested(PHINode* phi) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(phi->getParent());
    BasicBlock* latch = loop->getLoopLatch();
    std::vector<path_ty> paths = get_paths_from_to_loop(loop);
    Value* incoming_v = phi->getIncomingValueForBlock(latch);
    // z3::expr cur_rec = z3::ite(path_cond)

    std::vector<path_ty> valid_paths;
    for (auto path : paths) {
        // path_ty path_without_header(path.begin() + 1, path.end());
        z3::expr path_cond = path_condition_as_header_phis(path);
        z3::solver solver(z3ctx);
        solver.add(path_cond);
        auto res = solver.check();
        if (res == z3::sat || res == z3::unknown)
            valid_paths.push_back(path);
        // path_ty reversed_path(path.rbegin(), path.rend());
        // z3::expr cur_expr = _express_v_as_header_phis(incoming_v, reversed_path);
        // path_ty path_without_header(path.begin() + 1, path.end());
        // z3::expr path_cond = path_condition_as_header_phis(path_without_header);
        // errs() << path_cond.simplify().to_string() << "\n";
        // errs() << phi->getName() << " " << cur_expr.to_string() << "\n";
    }
    assert(valid_paths.size() >= 2);
    int sz = valid_paths.size();
    path_ty path = valid_paths[sz - 1];
    path_ty cur_path = valid_paths[sz - 2];
    path_ty reversed_path(path.rbegin(), path.rend());
    path_ty reversed_cur_path(cur_path.rbegin(), cur_path.rend());
    z3::expr dummy = z3ctx.bool_const(("nondet" + std::to_string(sz - 2)).c_str());
    z3::expr expr1 =_express_v_as_header_phis(incoming_v, reversed_path);
    z3::expr expr2 =_express_v_as_header_phis(incoming_v, reversed_cur_path);
    z3::expr expr = z3::ite(dummy, expr1, expr2);
    // print_path(path);
    // print_path(cur_path);
    for (int i = sz - 3; i >= 0; i--) {
        cur_path = valid_paths[i];
        path_ty reversed_cur_path(cur_path.rbegin(), cur_path.rend());
        dummy = z3ctx.bool_const(("nondet" + std::to_string(i)).c_str());
        z3::expr cur_expr =_express_v_as_header_phis(incoming_v, reversed_cur_path);
        expr = z3::ite(dummy, cur_expr, expr);
    }
    rec_ty res;
    res.insert_or_assign(v2z3(phi), expr);
    return res;
}

z3::expr
c2z3::path_condition_as_header_phis(path_ty& path) {
    return _path_condition_as_header_phis(path, 1);
}

z3::expr
c2z3::_path_condition_as_header_phis(path_ty& path, int start) {
    if (path.size() - start == 1) {
        return z3ctx.bool_val(true);
    }
    z3::expr post_cond = _path_condition_as_header_phis(path, start + 1);
    BasicBlock* cur_bb = path[start];
    BasicBlock* next_bb = path[start + 1];
    Instruction* term = cur_bb->getTerminator();
    BranchInst* branch = dyn_cast_or_null<BranchInst>(term);
    z3::expr local_cond = z3ctx.bool_val(true);
    if (branch->isConditional()) {
        bool is_negated = branch->getSuccessor(0) == next_bb ? false : true;
        path_ty reversed_path(path.begin(), path.begin() + start + 1);
        std::reverse(reversed_path.begin(), reversed_path.end());
        local_cond = _express_v_as_header_phis(branch->getOperand(0), reversed_path);
        local_cond = is_negated ? !local_cond : local_cond;
    }
    z3::expr res_cond = local_cond && post_cond;
    return res_cond;
}

z3::expr c2z3::_express_v_as_header_phis(Value* v, path_ty& reversed_path) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        int svalue = CI->getSExtValue();
        return is_bool(v) ? z3ctx.bool_val(svalue) : z3ctx.int_val(svalue);
    }
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    BasicBlock* bb = inst->getParent();
    // Loop* loop = LI.getLoopFor(bb);
    // int dim = LI.getLoopDepth(bb);
    // if (loop != target_loop) {
    //     return v2z3(v);
        // return v2z3(v, dim, false);
    // }
    if (bb == reversed_path.back() && isa<PHINode>(v)) {
        return v2z3(v);
        // return v2z3(v, dim, false);
    }

    auto found_bb = std::find(reversed_path.begin(), reversed_path.end(), bb);
    if (found_bb == reversed_path.end()) {
        return v2z3(v);
    }
    path_ty path(found_bb, reversed_path.end());
    BasicBlock* prev_bb = *(found_bb + 1);
    z3::func_decl f = get_z3_function(v);
    z3::expr_vector args = get_args(0);
    z3::expr_vector res(z3ctx);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = _express_v_as_header_phis(op0, path);
        z3::expr z3op1 = _express_v_as_header_phis(op1, path);
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
        z3::expr z3op0 = _express_v_as_header_phis(op0, path);
        z3::expr z3op1 = _express_v_as_header_phis(op1, path);
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
        z3::expr cond = _express_v_as_header_phis(CI->getOperand(0), path);
        z3::expr first = _express_v_as_header_phis(CI->getOperand(1), path);
        z3::expr second = _express_v_as_header_phis(CI->getOperand(2), path);
        return z3::ite(cond, first, second);
    } else if (auto CI = dyn_cast_or_null<CallInst>(inst)) {
        // all calls are treated as unknown values;
        return z3ctx.int_const("unknown");
    } else if (auto phi = dyn_cast_or_null<PHINode>(inst)) {
        // z3::expr ite = phi2ite_header(CI);
        Value* incoming_v = phi->getIncomingValueForBlock(prev_bb);
        path_ty new_path(found_bb + 1, reversed_path.end());
        return _express_v_as_header_phis(incoming_v, new_path);
        // if (ite) {
        //     return ite;
        // } else {
        //     throw UnimplementedOperationException(opcode);
        // }
    } else if (auto CI = dyn_cast_or_null<SExtInst>(inst)) {
        return _express_v_as_header_phis(CI->getOperand(0), path);
    } else if (auto CI = dyn_cast_or_null<ZExtInst>(inst)) {
        return _express_v_as_header_phis(CI->getOperand(0), path);
    } else if (auto CI = dyn_cast_or_null<LoadInst>(inst)) {
        z3::func_decl arr_f = get_array_function(inst);
        array_access_ty access = get_array_access_from_load_store(CI);
        z3::expr_vector indices(z3ctx);
        for (auto u : access.second) {
            Value* v = u->get();
            indices.push_back(_express_v_as_header_phis(v, path));
        }
        z3::expr_vector arr_n_args = merge_vec(indices, args);
        return arr_f(arr_n_args);
    } else {
        throw UnimplementedOperationException(opcode);
    }
    // z3::expr final_res = z3ctx.bool_val(true);
    // for (auto e : res) {
    //     final_res = final_res && e;
    // }
    // return final_res;
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

z3::expr c2z3::get_z3_N(Loop* loop) {
    int dim = loop->getLoopDepth();
    std::string N_idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(dim - 1);
    return z3ctx.int_const(N_idx.data());
}

int c2z3::get_m_phi_def_id(MemoryAccess* access) {
    assert(isa<MemoryDef>(access) || isa<MemoryPhi>(access));
    if (auto def = dyn_cast_or_null<MemoryDef>(access)) {
        return def->getID();
    }
    auto phi = dyn_cast_or_null<MemoryPhi>(access);
    return phi->getID();
}

z3::expr_vector c2z3::inst2z3(Instruction* inst, BasicBlock* prev_bb=nullptr) {
    z3::expr_vector res(z3ctx);
    if (auto CI = dyn_cast_or_null<CallInst>(inst)) {
        return res;
    }
    Type* tp = inst->getType();
    const char* var_name = inst->getName().data();
    bool is_bool = tp->isIntegerTy(1);
    BasicBlock* block = inst->getParent();
    z3::expr_vector initial_res(z3ctx);
    auto old_array_z3_function = array_z3_func;
    z3::func_decl f = get_z3_function(inst);
    z3::expr_vector args = get_args(0);
    bool solved = false;
    int opcode = inst->getOpcode();
    if (solved) {
        // pass
    } else if (inst->isBinaryOp()) {
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = v2z3(op0);
        z3::expr z3op1 = v2z3(op1);
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
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = v2z3(op0);
        z3::expr z3op1 = v2z3(op1);
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
        } else if (called_name == "assume_abort_if_not") {
            res.push_back(use2z3(&CI->getOperandUse(0)));
        }
    } else if (auto CI = dyn_cast_or_null<PHINode>(inst)) {
        if (CI->getNumIncomingValues() == 1) {
            res.push_back(f(args) == v2z3(CI->getOperand(0)));
        } else if (prev_bb) {
            int idx = CI->getBasicBlockIndex(prev_bb);
            assert(idx != -1);
            Value* instantiated = CI->getOperand(idx);
            z3::expr z3_instantiated = v2z3(instantiated);
            res.push_back(f(args) == z3_instantiated);
        } else {
            errs() << inst->getName() << "\n";
            assert(false);
            // for (int i = 0; i < CI->getNumIncomingValues(); i++) {
            //     BasicBlock* cur_bb = inst->getParent();
            //     BasicBlock* in_bb = CI->getIncomingBlock(i);
            //     Use* op = &CI->getOperandUse(i);
            //     z3::expr z3_op = use2z3(op);
            //     // phi in header
            //     if (loop && loop->getHeader() == block) {
            //         std::string n_idx = "n" + std::to_string(dim - 1);
            //         std::string N_idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(dim - 1);
            //         z3::expr z3_nidx = z3ctx.int_const(n_idx.data());
            //         z3::expr z3_Nidx = z3ctx.int_const(N_idx.data());
            //         if (!loop->contains(in_bb)) {
            //             // initial
            //             // args[dim - 1] = z3ctx.int_val(0);
            //             args.pop_back();
            //             args.push_back(z3ctx.int_val(0));
            //             initial_res.push_back(f(args) == z3_op);
            //         } else if (loop->getLoopLatch() == in_bb) {
            //             // inductive
            //             args.pop_back();
            //             args.push_back(z3_nidx + 1);
            //             // args[dim - 1] = z3_nidx + 1;
            //             // res.push_back(z3::implies(z3_nidx >= 0, f(args) == z3_op));
            //             res.push_back(f(args) == z3_op);
            //         } else {
            //             throw UnimplementedOperationException(opcode);
            //         }
            //     } else {
            //         pc_type pc = path_condition(in_bb);
            //         z3::expr cond = pc.first; 
            //         // z3::expr cond = path_condition(in_bb);
            //         // z3::expr local_cond = path_condition_b2b(in_bb, cur_bb);
            //         auto cond_negated = path_condition_b2b(in_bb, cur_bb);
            //         z3::expr local_cond = use2z3(cond_negated.first);
            //         Loop* prev_loop = LI.getLoopFor(in_bb);
            //         if (prev_loop && prev_loop->contains(cur_bb)) {
            //             local_cond = cond_negated.second ? !local_cond : local_cond;
            //         } else if (prev_loop) {
            //             int prev_dim = LI.getLoopDepth(prev_loop->getHeader());
            //             z3::expr_vector N_args = get_args(prev_dim, true, false, true, prev_loop);
            //             z3::expr_vector n1_args = get_args(prev_dim, false, true, true);
            //             local_cond = cond_negated.second ? !local_cond : local_cond;
            //             local_cond = local_cond.simplify().substitute(n1_args, N_args);
            //             cond = cond.simplify().substitute(n1_args, N_args);
            //         } else {
            //             local_cond = z3ctx.bool_val(true);
            //         }
            //         res.push_back(z3::implies(cond && local_cond, f(args) == z3_op));
            //     }
            // }
        }
    } else if (auto CI = dyn_cast_or_null<AllocaInst>(inst)) {
        // Value* sz = CI->getArraySize();
        // Type* ty = CI->getAllocatedType();
        // int num_e = 1;
        // if (auto arr_ty = dyn_cast_or_null<ArrayType>(ty))
        //     num_e = arr_ty->getNumElements();
        // z3::expr_vector arr_dim_info(z3ctx);
        // arr_dim_info.push_back(v2z3(sz, dim, false) * num_e);
        // array_info.insert_or_assign(inst, arr_dim_info);
        // array_index[inst] = 0;
        // array_z3_func.insert_or_assign(inst, f);
        // array_def_block.insert_or_assign(inst, CI->getParent());
    } else if (auto CI = dyn_cast_or_null<LoadInst>(inst)) {
        array_access_ty access = get_array_access_from_load_store(CI);
        MemoryAccess* m_access = get_mem_use(inst);
        z3::func_decl arr_f = get_array_function(inst);
        z3::expr used_array = use2z3(&CI->getOperandUse(0));
        z3::expr_vector old_args = used_array.args();
        z3::expr e = f(args) == arr_f(old_args);
        res.push_back(e);
    } else if (auto CI = dyn_cast_or_null<StoreInst>(inst)) {
        if (encounter_mem_phi(inst)) {
            z3::expr_vector phi_axioms = mem_header_phi2z3(inst);
            combine_vec(res, phi_axioms);
        }
        array_access_ty access = get_array_access_from_load_store(CI);
        int arity = access.second.size();
        auto arr_args = get_arr_args(arity);
        z3::expr_vector access_args_z3 = arr_access2z3(access.second);
        z3::expr premise = pairwise_eq(arr_args, access_args_z3);

        z3::expr_vector all_args = get_arr_args(arity);
        z3::expr_vector all_old_args = get_arr_args(arity);

        z3::func_decl old_f = get_array_function(inst);
        int old_dim = old_f.arity() - arity;
        z3::expr_vector old_args = get_args(old_dim, false, true, false);

        if (encounter_mem_phi(inst)) {
            old_args = get_args(old_dim, false, false, false);
        }

        combine_vec(all_args, args);
        combine_vec(all_old_args, old_args);
        // combine_vec(all_args_frame, args_frame);
        Use* stored_v = &CI->getOperandUse(0);

        z3::expr e = f(all_args) == ite(premise, use2z3(stored_v), old_f(all_old_args));
        res.push_back(e);
        array_def_block.insert_or_assign(access.first, CI->getParent());
    } else if (auto CI = dyn_cast_or_null<SExtInst>(inst)) {
        res.push_back(f(args) == v2z3(CI->getOperand(0)));
    } else if (auto CI = dyn_cast_or_null<ZExtInst>(inst)) {
        res.push_back(f(args) == v2z3(CI->getOperand(0)));
    } else if (auto CI = dyn_cast_or_null<TruncInst>(inst)) {
        res.push_back(f(args) == v2z3(CI->getOperand(0)));
    } else if (auto CI = dyn_cast_or_null<GetElementPtrInst>(inst)) {

    } else {
        throw UnimplementedOperationException(opcode);
    }
    return res;
    // return z3::forall(params, res);
    // z3::expr_vector forall_res(z3ctx);
    // z3::expr loop_range = z3ctx.bool_val(true);
    // for (auto a : loop_args) {
    //     loop_range = loop_range && a >= 0;
    // }
    // // loop_range.simplify();
    // for (auto e : res) {
    //     if (loop_args.size() > 0 || arr_args.size() > 0) {
    //         z3::expr_vector forall_args(z3ctx);
    //         combine_vec(forall_args, loop_args);
    //         combine_vec(forall_args, arr_args);
    //         forall_res.push_back(z3::forall(forall_args, z3::implies(loop_range, e)));
    //     } else {
    //         forall_res.push_back(e);
    //     }
    // }
    // for (auto e : initial_res) {
    //     forall_res.push_back(e);
    // }
    // return forall_res;
}

z3::expr c2z3::m_as_header_phi(Value* array, MemoryAccess* access, Loop* loop) {
    if (is_m_header_phi(access, loop) || !loop->contains(access->getBlock())) {
        z3::func_decl arr_f = get_array_function(array, access);
        int dim = loop->getLoopDepth();
        int arity = arr_f.arity() - dim;
        z3::expr_vector n_args = get_args(dim, false, false, false);
        z3::expr_vector arr_args = get_access_index(array);
        z3::expr_vector all_args = merge_vec(arr_args, n_args);
        return arr_f(all_args);
    }
    throw UnimplementedOperationException("not implemented yet");
}

bool c2z3::is_m_header_phi(MemoryAccess* access, Loop* loop) {
    LoopInfo& LI = LIs.at(main);
    return loop->getHeader() == access->getBlock() && isa<MemoryPhi>(access);
}

z3::expr c2z3::pairwise_eq(z3::expr_vector e1, z3::expr_vector e2) {
    z3::expr res = z3ctx.bool_val(true);
    assert(e1.size() == e2.size());
    for (int i = 0; i < e1.size(); i++) {
        res = res && e1[i] == e2[i];
    }
    return res.simplify();
}

bool c2z3::encounter_mem_phi(Value* v) {
    MemoryAccess* m_access_use = get_mem_use(v);
    return isa<MemoryPhi>(m_access_use);
}

MemoryAccess* c2z3::get_mem_use(Value* v) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    MemorySSA& MSSA = MSSAs.at(main);
    array_access_ty access = get_array_access_from_load_store(v);
    MemoryAccess* m_access = MSSA.getMemoryAccess(inst);
    auto m_access_def = dyn_cast_or_null<MemoryUseOrDef>(m_access);
    MemoryAccess* m_access_use = m_access_def->getDefiningAccess();
    return m_access_use;
}

z3::expr_vector c2z3::mem_header_phi2z3(Value* v) {
    MemoryAccess* m_access = get_mem_use(v);
    auto m_phi = dyn_cast_or_null<MemoryPhi>(m_access);
    BasicBlock* bb = m_phi->getBlock();
    Loop* loop = get_loop(bb);
    BasicBlock* latch = loop->getLoopLatch();
    int latch_idx = m_phi->getBasicBlockIndex(latch);
    assert(m_phi->getNumIncomingValues() == 2);
    int initial_idx = m_phi->getNumIncomingValues() - latch_idx - 1;
    MemoryAccess* initial_access = m_phi->getIncomingValue(initial_idx);
    MemoryAccess* latch_access = m_phi->getIncomingValue(latch_idx);
    auto initial_access_def = dyn_cast_or_null<MemoryDef>(initial_access);
    auto latch_access_def = dyn_cast_or_null<MemoryDef>(latch_access);
    z3::expr_vector res_initial_part = initial_mem_phi2z3(initial_access, m_phi);
    z3::expr_vector res_latch_part = latch_mem_phi2z3(latch_access, m_phi);
    // for (auto e : res_initial_part) {
    //     errs() << e.to_string() << "\n";
    // }
    // for (auto e : res_latch_part) {
    //     errs() << e.to_string() << "\n";
    // }
    return merge_vec(res_initial_part, res_latch_part);
}

int c2z3::get_dim(BasicBlock* bb) {
    LoopInfo& LI = LIs.at(main);
    return LI.getLoopDepth(bb);
}

z3::expr_vector c2z3::latch_mem_phi2z3(MemoryAccess* latch_access, MemoryPhi* phi) {
    z3::expr_vector res(z3ctx);
    int old_id = 0;
    auto access_def = dyn_cast_or_null<MemoryDef>(latch_access);
    if (access_def) old_id = access_def->getID();
    BasicBlock* bb = phi->getBlock();
    int dim = get_dim(bb);
    for (auto info : array_info) {
        Value* array = info.first;
        int arity = info.second.size();
        z3::expr_vector args_n = get_args(dim, false, true, false);
        z3::expr_vector arr_args = get_arr_args(arity);
        z3::expr_vector all_args = merge_vec(arr_args, args_n);

        z3::func_decl f = get_array_function(array, phi->getID(), arity + dim);
        z3::func_decl old_f = get_array_function(array, old_id, arity + dim);
        res.push_back(f(all_args) == old_f(all_args));
    }
    return res;
}

z3::expr_vector c2z3::initial_mem_phi2z3(MemoryAccess* initial_access, MemoryPhi* phi) {
    z3::expr_vector res(z3ctx);
    int old_id = 0;
    auto access_def = dyn_cast_or_null<MemoryDef>(initial_access);
    if (access_def) old_id = access_def->getID();
    BasicBlock* bb = phi->getBlock();
    int dim = get_dim(bb);
    BasicBlock* old_bb = initial_access->getBlock();
    int old_dim = get_dim(old_bb);
    Loop* loop = get_loop(old_bb);
    for (auto info : array_info) {
        Value* array = info.first;
        int arity = info.second.size();
        z3::expr_vector args_N = get_args_N(loop);
        z3::expr_vector args_0 = get_args_0(dim);
        z3::expr_vector arr_args = get_arr_args(arity);

        z3::expr_vector all_args = merge_vec(arr_args, args_0);
        z3::expr_vector old_all_args = merge_vec(arr_args, args_N);

        z3::func_decl f = get_array_function(array, phi->getID(), arity + dim);
        z3::func_decl old_f = get_array_function(array, old_id, arity + old_dim);
        res.push_back(f(all_args) == old_f(old_all_args));
    }
    return res;
}

z3::expr_vector c2z3::get_args_N(Loop* loop) {
    int dim = loop ? loop->getLoopDepth() : 0;
    z3::expr_vector args = get_args(dim, false, false, false);
    if (dim > 0) {
        args.pop_back();
        args.push_back(get_z3_N(loop));
    }
    return args;
}

z3::expr_vector c2z3::get_args_0(int dim) {
    z3::expr_vector args = get_args(dim, false, false, false);
    args.pop_back();
    args.push_back(z3ctx.int_val(0));
    return args;
}

std::string c2z3::get_array_name(Value* v, int mem_id) {
    std::string array_name = std::string(v->getName().data()) + "_" + std::to_string(mem_id);
    return array_name;
}

Loop* c2z3::get_loop(BasicBlock* bb) {
    LoopInfo& LI = LIs.at(main);
    return LI.getLoopFor(bb);
}

z3::expr_vector c2z3::arr_access2z3(const std::vector<Use*>& args) {
    z3::expr_vector res(z3ctx);
    for (Use* u : args) {
        res.push_back(use2z3(u));
    }
    return res;
}

z3::expr_vector c2z3::get_arr_args(int arity) {
    z3::expr_vector args(z3ctx);
    for (int i = 0; i < arity; i++) {
        std::string name = "a_" + std::to_string(i);
        args.push_back(z3ctx.int_const(name.data()));
    }
    return args;
}

z3::expr c2z3::v2z3(Value* v, int dim, int plus) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        IntegerType* i_type = CI->getType();
        bool is_bool = i_type->isIntegerTy(1);
        if (is_bool)
            return z3ctx.bool_val(CI->getZExtValue());
        else
            return z3ctx.int_val(CI->getSExtValue());
    }
    int arity = get_arity(v);
    z3::func_decl f = get_z3_function(v, arity + dim);
    z3::expr_vector args = get_args(dim, false, plus, true);
    z3::expr_vector arr_args = get_access_index(v);
    combine_vec(arr_args, args);
    return f(arr_args);
}

z3::expr_vector c2z3::get_access_index(Value* v) {
    z3::expr_vector res(z3ctx);
    if (auto gep = dyn_cast_or_null<GetElementPtrInst>(v)) {
        array_access_ty access = get_array_access_from_gep(gep);
        for (Use* u : access.second) {
            res.push_back(use2z3(u));
        }
    }
    return res;
}

int c2z3::get_arity(Value* v) {
    if (auto gep = dyn_cast_or_null<GetElementPtrInst>(v)) {
        array_access_ty access = get_array_access_from_gep(gep);
        return array_info.at(access.first).size();
    } else if (isa<StoreInst>(v)) {
        array_access_ty access = get_array_access_from_load_store(v);
        return array_info.at(access.first).size();
    }
    return 0;
}

bool c2z3::is_header_phi(Value* v, Loop* loop) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    if (!inst || !loop) return false;
    BasicBlock* bb = inst->getParent();
    BasicBlock* header = loop->getHeader();
    return bb == header && isa<PHINode>(v);
}

z3::expr c2z3::use2z3(Use* u) {
    if (u == nullptr) return z3ctx.bool_val(true);
    Value* use_def = u->get();
    Type* tp = use_def->getType();
    const char* var_name = use_def->getName().data();
    bool is_bool = tp->isIntegerTy(1);
    if (auto CI = dyn_cast<ConstantInt>(use_def)) {
        if (is_bool) {
            return z3ctx.bool_val(CI->getZExtValue());
        } else {
            return z3ctx.int_val(CI->getSExtValue());
        }
    }

    LoopInfo& LI = LIs.at(main);
    auto CI = dyn_cast<Instruction>(use_def);
    int dim = LI.getLoopDepth(CI->getParent());
    int arity = get_arity(use_def);

    z3::func_decl f = get_z3_function(u);

    Value* user = u->getUser();
    auto user_inst = dyn_cast<Instruction>(user);
    BasicBlock* user_block = user_inst->getParent();
    BasicBlock* def_block = CI->getParent();
    if (auto gep = dyn_cast_or_null<GetElementPtrInst>(use_def)) {
        array_access_ty access = get_array_access_from_gep(gep);
        def_block = array_def_block.at(access.first);
        dim = LI.getLoopDepth(def_block);
    }
    Loop* user_loop = LI.getLoopFor(user_block);
    Loop* def_loop = LI.getLoopFor(def_block);

    z3::expr_vector args = get_args(dim, false, true, false);
    z3::expr_vector arr_args = get_access_index(use_def);
    if (is_header_phi(use_def, def_loop)) {
        args = get_args(dim, false, false, false);
    }
    bool is_n = false;
    if (def_loop && def_loop->contains(user_inst)) {
        // if (is_n) {
        //     try {
        //         if (user_loop) {
        //             args.pop_back();
        //             std::string idx = "n" + std::to_string(dim - 1);
        //             args.push_back(z3ctx.int_const(idx.data()));
        //             // args[loop->getLoopDepth() - 1] = args[loop->getLoopDepth() - 1] + 1;
        //         }
        //     } catch (...) {

        //     }
        // }
    } else if (def_loop) {
        args.pop_back();
        std::string idx = "N_" + std::to_string(loop2idx[def_loop]) + "_" + std::to_string(dim - 1);
        args.push_back(z3ctx.int_const(idx.data()));
    }
    // z3::func_decl f = z3ctx.function(var_name, params, ret_sort);
    z3::expr_vector all_args = merge_vec(arr_args, args);
    return f(all_args);
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
        } else {
            throw UnimplementedOperationException(opcode);
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
        } else {
            throw UnimplementedOperationException(opcode);
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
    } else if (auto select = dyn_cast_or_null<SelectInst>(v)) {
        z3::expr cond = as_loop_expression(&select->getOperandUse(0));
        z3::expr op0 = as_loop_expression(&select->getOperandUse(1));
        z3::expr op1 = as_loop_expression(&select->getOperandUse(2));
        return z3::ite(cond, op0, op1);
    } else {
        throw UnimplementedOperationException(opcode);
    }
}

// z3::expr_vector c2z3::all2z3(Instruction* inst) {
//     if (visited_inst.contains(inst)) {
//         return z3::expr_vector(z3ctx);
//     }
//     visited_inst.insert(inst);
//     LoopInfo& LI = LIs.at(main);
//     Loop* loop = LI.getLoopFor(inst->getParent());
//     z3::expr_vector res = inst2z3(inst);
//     std::set<Loop*> all_loops;
//     for (int i = 0; i < inst->getNumOperands(); i++) {
//         Value* cur_v = inst->getOperand(i);
//         if (auto CI = dyn_cast<Instruction>(cur_v)) {
//             z3::expr_vector cur_vec = all2z3(CI);
//             combine_vec(res, cur_vec);
//         }
//         if (auto phi = dyn_cast<PHINode>(cur_v)) {
//             std::set<Use*> uses = get_bb_conditions(phi->getParent());
//             for (Use* u : uses) {
//                 if (u) {
//                     z3::expr_vector cur_vec = all2z3(dyn_cast<Instruction>(u->get()));
//                     combine_vec(res, cur_vec);
//                 }
//             }
//         }
//     }
//     if (loop && !visited_loops.contains(loop)) {
//         visited_loops.insert(loop);
//         pc_type loop_pc = loop_condition(loop);
//         res.push_back(loop_pc.first);
//     }
//     return res;
// }

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

z3::expr c2z3::assertion2z3(Use* a) {
    z3::expr res = z3ctx.bool_val(true);
    Value* v = a->get();
    int dim = get_dim(a);
    z3::expr_vector n_args = get_args(dim, false, false, false);
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    Loop* loop = nullptr;
    if (inst) loop = LI.getLoopFor(inst->getParent());
    z3::expr_vector N_args = get_args(dim, true, false, false, loop);
    z3::expr_vector n_range(z3ctx);
    // std::transform(n_args.begin(), n_args.end(), std::back_inserter(n_range), [](z3::expr e) { return e >= 0; });
    // z3::expr premise = std::accumulate(n_args.begin(), n_args.end(), z3ctx.int_val(1), [](const z3::expr& e1, const z3::expr& e2) { return e1 >= 0 && e2 >= 0; }).simplify();
    z3::expr premise = z3ctx.bool_val(true);
    for (int i = 0; i < dim; i++) {
        premise = premise && n_args[i] >= 0 && n_args[i] < N_args[i];
    }
    z3::expr body = use2z3(a);
    if (!body.is_bool()) {
        body = (body != 0);
    }
    if (dim > 0)
        return z3::forall(n_args, z3::implies(premise, body));
    else
        return body;

}

z3::expr_vector c2z3::simplify_using_closed(z3::expr e) {
    z3::expr n = z3ctx.int_const("n0");
    z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    src.push_back(n);
    dst.push_back(free_var);
    z3::expr_vector res(z3ctx);

    z3::expr cur_e = e;
    for (rec_ty c : cached_closed) {
        for (auto p : c) {
            if (p.first.is_app() && p.first.args().size() > 0 && p.first.args()[0].to_string() == "n0") {
                z3::func_decl f = p.first.decl();
                z3::expr closed_form = p.second.substitute(src, dst);
                z3::func_decl_vector fs(z3ctx);
                fs.push_back(f);
                z3::expr_vector closed_forms(z3ctx);
                closed_forms.push_back(closed_form);
                cur_e = cur_e.substitute(fs, closed_forms);
            }
        }
    }
    res.push_back(cur_e);
    // res.push_back(e);

    return res;
}

z3::expr_vector c2z3::simplify_using_closed(z3::expr_vector vec) {
    // return vec;
    z3::expr n = z3ctx.int_const("n0");
    z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    src.push_back(n);
    dst.push_back(free_var);
    z3::expr_vector res(z3ctx);
    for (auto e : vec) {
        z3::expr_vector cur_e = simplify_using_closed(e);
        // errs() << "- " <<  e.to_string() << "\n";
        // errs() << "- " <<  cur_e.to_string() << "\n";
        combine_vec(res, cur_e);
    }
    return res;
}

int c2z3::get_dim(Use* a) {
    // User* user = a->getUser();
    Value* v = a->get();
    auto inst = dyn_cast_or_null<Instruction>(v);
    if (!inst) return 0;
    LoopInfo& LI = LIs.at(main);
    return LI.getLoopDepth(inst->getParent());
}

validation_type c2z3::check_assert(Use* a, int out_idx) {
    User* user = a->getUser();
    auto CI = dyn_cast_or_null<Instruction>(user);
    std::vector<path_ty> paths = get_paths_from_to(&main->getEntryBlock(), CI->getParent());
    validation_type res = correct;
    for (int i = 0; i < paths.size(); i++) {
        auto p = paths[i];
        z3::solver s(z3ctx);
        s.add(path2z3(p));
        // z3::expr dummy = z3ctx.int_const("dummy");
        // z3::expr dummy2 = z3ctx.int_const("dummy2");
        // z3::expr_vector dummies(z3ctx);
        // dummies.push_back(dummy);
        // dummies.push_back(dummy2);
        // z3::expr body = dummy*(1+2*dummy*dummy+3*dummy);
        // s.add(z3::forall(dummies, z3::implies(!(dummy2 >= 1 && dummy - dummy2 <= -2) && dummy2 >= 0 && !(dummy2 <= dummy), dummy2 == dummy + 1 || dummy < 0)));
        // s.add(z3::forall(dummy, 6*(body/6) == body));
        // body = dummy*dummy*(1 + dummy*dummy + 2*dummy);
        // s.add(z3::forall(dummy, 4*(body/4) == body));
        // body = -1*dummy + 6*dummy*dummy*dummy*dummy*dummy + 10*dummy*dummy*dummy + 15*dummy*dummy*dummy*dummy;
        // s.add(z3::forall(dummy, 30*(body/30) == body));
        // body = -1*dummy*dummy+ 2*dummy*dummy*dummy*dummy*dummy*dummy + 5*dummy*dummy*dummy*dummy + 6*dummy*dummy*dummy*dummy*dummy;
        // s.add(z3::forall(dummy, 12*(body/12) == body));
        // body = dummy*(1 + dummy);
        // s.add(z3::forall(dummy, 2*(body/2) == body));
        // int acc = 1;
        // z3::expr e = dummy;
        // for (int j = 1; j < 6; j++) {
        //     acc *= (j + 1);
        //     e = e*(j + dummy);
        //     s.add(z3::forall(dummy, acc*(e/acc) == e));
        // }
        std::string filename = "tmp/tmp" + std::to_string(out_idx) + "_path_"+ std::to_string(i) + ".smt2";
        std::ofstream out(filename);
        z3::expr neg_assertion = !assertion2z3(a);
        s.add(simplify_using_closed(neg_assertion));
        // s.add(z3::forall(dummies, z3::implies(dummy == 0 || dummy == dummy2, dummy*dummy2 == dummy*dummy)));
        // z3::expr body = dummy*(1+2*dummy*dummy+3*dummy);
        // s.add(z3::forall(dummies, z3::implies(!(dummy2 >= 1 && dummy - dummy2 <= -2) && dummy2 >= 0 && !(dummy2 <= dummy), dummy2 == dummy + 1 || dummy < 0)));
        // s.add(z3::forall(dummy, 6*(body/6) == body));
        // body = dummy*dummy*(1 + dummy*dummy + 2*dummy);
        // s.add(z3::forall(dummy, 4*(body/4) == body));
        // body = -1*dummy + 6*dummy*dummy*dummy*dummy*dummy + 10*dummy*dummy*dummy + 15*dummy*dummy*dummy*dummy;
        // s.add(z3::forall(dummy, 30*(body/30) == body));
        // body = -1*dummy*dummy+ 2*dummy*dummy*dummy*dummy*dummy*dummy + 5*dummy*dummy*dummy*dummy + 6*dummy*dummy*dummy*dummy*dummy;
        // s.add(z3::forall(dummy, 12*(body/12) == body));
        // body = dummy*(1 + dummy);
        // s.add(z3::forall(dummy, 2*(body/2) == body));
        out << s.to_smt2().data() << "\n";
        out.close();

        // auto val_res = s.check();
        smt_solver solver;
        auto val_res = solver.check(filename, 60*1000);
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
            Value* cond = br->getOperand(0);
            res = v2z3(cond);
            res = to == br->getSuccessor(0) ? res : !res;
        }
    }
    return res;
}


z3::expr_vector c2z3::bb2z3(BasicBlock* bb, BasicBlock* prev_bb=nullptr) {
    z3::expr_vector res(z3ctx);
    for (Instruction& inst : *bb) {
        if (bb->getTerminator() == &inst) continue;
        z3::expr_vector local_exprs = inst2z3(&inst, prev_bb);
        combine_vec(res, local_exprs);
    }
    return res;
}

z3::expr_vector c2z3::loop2z3(Loop* loop, BasicBlock* prev_bb=nullptr) {
    z3::expr_vector res(z3ctx);
    for (BasicBlock* loop_bb : loop->getBlocks()) {
        z3::expr_vector local_exprs = bb2z3(loop_bb);
        combine_vec(res, local_exprs);
    }
    return res;
}

z3::expr_vector c2z3::path2z3(path_ty p) {
    cached_closed.clear();
    z3::expr_vector axioms(z3ctx);
    BasicBlock* prev_bb = nullptr;
    LoopInfo& LI = LIs.at(main);
    for (BasicBlock* bb : p) {
        if (prev_bb) {
            axioms.push_back(path_condition_one_stride(prev_bb, bb));
        }
        Loop* loop = LI.getLoopFor(bb);
        if (loop) {
            assert(loop->getLoopDepth() == 1);
            visited_loops.insert(loop);
            // z3::expr_vector loop_exprs = loop2z3(loop);
            // combine_vec(axioms, loop_exprs);
            prev_bb = bb;
        // } else if (loop) {
        //     prev_bb = bb;
        //     throw UnimplementedOperationException("Do not support nested loop with depth larger than 2");
        } else {
            z3::expr_vector local_exprs = bb2z3(bb, prev_bb);
            combine_vec(axioms, local_exprs);
            prev_bb = bb;
        }
    }
    // z3::expr n = z3ctx.int_const("n0");
    // z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
    // std::vector<closed_form_ty> closed;
    for (Loop* loop : visited_loops) {
        auto res_and_solver = solve_loop(loop);
        closed_form_ty res = res_and_solver.first;
        for (auto pair : res) {
            axioms.push_back(pair.first == pair.second);
        }
        // for (auto pair : res) {
        //     errs() << pair.first.to_string() << ' ' << pair.second.to_string() << "\n";
        // }
        z3::expr bnd = loop_bound(loop, res_and_solver.second);
        axioms.push_back(bnd);
        // z3::expr_vector ns(z3ctx);
        // z3::expr_vector Ns(z3ctx);
        // ns.push_back(n);
        // Ns.push_back(z3ctx.int_const(("N_" + std::to_string(loop2idx[loop]) + "_0").data()));
        // if (!res.empty()) {
        //     closed.push_back(res);
        //     // z3::expr ind_var = z3ctx.int_const("n0");
        //     for (auto r : res) {
        //         z3::expr k = r.first;
        //         axioms.push_back(z3::forall(n, z3::implies(n >= 0, k == r.second)));
        //         axioms.push_back(k.substitute(ns, Ns) == r.second.substitute(ns, Ns));
        //     }
        // }
    }
    // // z3::expr_vector src(z3ctx);
    // // z3::expr_vector dst(z3ctx);
    // // src.push_back(n);
    // // dst.push_back(free_var);
    // cached_closed = closed;
    // z3::expr_vector new_axioms = simplify_using_closed(axioms);
    // z3::expr_vector new_axioms = axioms;
    // for (auto e : axioms) {
    //     z3::expr cur_e = e;
    //     for (rec_ty c : closed) {
    //         for (auto p : c) {
    //             z3::func_decl f = p.first.decl();
    //             z3::expr closed_form = p.second.substitute(src, dst);
    //             // errs() << f.to_string() << " = " << closed_form.to_string() << "\n";
    //             z3::func_decl_vector fs(z3ctx);
    //             fs.push_back(f);
    //             z3::expr_vector closed_forms(z3ctx);
    //             closed_forms.push_back(closed_form);
    //             cur_e = cur_e.substitute(fs, closed_forms);
    //         }
    //     }
    //     new_axioms.push_back(cur_e);
    // }
    return axioms;
    // return new_axioms;
}

std::pair<closed_form_ty, rec_solver>
c2z3::solve_loop(Loop* loop) {
    rec_ty recs = loop2rec(loop);
    z3::expr_vector res(z3ctx);
    initial_ty initials = loop2initial(loop);
    auto rec_s = rec_solver(z3ctx);
    rec_s.set_eqs(recs);
    rec_s.add_initial_values(initials.first, initials.second);
    rec_s.solve();
    closed_form_ty rec_res = rec_s.get_res();
    closed_form_ty new_rec_res = rec_res;

    for (auto bb : loop->getBlocks()) {
        for (auto& inst : *bb) {
            if (inst.hasName() && !isa<GetElementPtrInst>(inst) && !isa<StoreInst>(inst) && !isa<LoadInst>(inst)) {
                z3::expr cur_e(z3ctx);
                try {
                    cur_e = express_v_as_header_phis(&inst);
                } catch (...) {
                    continue;
                }
                for (auto p : rec_res) {
                    // if (p.first.is_app() && p.first.args().size() > 0 && (p.first.args()[0].to_string() == "n0")) {
                    if (p.first.is_const()) {
                        z3::func_decl f = p.first.decl();
                        z3::expr closed_form = p.second; // .substitute(src, dst);
                        z3::func_decl_vector fs(z3ctx);
                        fs.push_back(f);
                        z3::expr_vector closed_forms(z3ctx);
                        closed_forms.push_back(closed_form);
                        cur_e = cur_e.substitute(fs, closed_forms);
                    }
                }
                z3::func_decl cur_f = get_z3_function(&inst);
                z3::expr_vector args = get_args(0);
                new_rec_res.insert_or_assign(cur_f(args), cur_e);
            }
        }
    }
    // for (auto pair : new_rec_res) {
    //     errs() << pair.first.to_string() << ' ' << pair.second.to_string() << "\n";
    // }
    // if (!rec_res.empty()) {
    //     // closed.push_back(res);
    //     z3::expr ind_var = z3ctx.int_const("n0");
    // }
    z3::expr_vector ns(z3ctx);
    z3::expr_vector Ns(z3ctx);
    ns.push_back(rec_s.get_ind_var());
    Ns.push_back(z3ctx.int_const("N0"));
    closed_form_ty final_res;
    for (auto pair : new_rec_res) {
        z3::expr lhs = pair.first;
        z3::expr rhs = pair.second.substitute(ns, Ns);
        final_res.insert_or_assign(lhs.substitute(ns, Ns), rhs);
    }
    return {final_res, rec_s};
}

// validation_type c2z3::check_assert_backward(Use* a, int out_idx) {
//     visited_loops.clear();
//     visited_inst.clear();
// 
//     z3::solver s(z3ctx);
// 
//     User* user = a->getUser();
//     int dim = 0;
//     if (!isa<Constant>(user)) {
//         auto CI = dyn_cast_or_null<Instruction>(user);
//         LoopInfo& LI = LIs.at(main);
//         dim = LI.getLoopDepth(CI->getParent());
//     }
//     z3::expr_vector args = get_pure_args(dim, false);
//     z3::expr non_neg_args_cond = get_non_neg_args_cond(dim);
// 
//     if (args.size() > 0) {
//         s.add(!z3::forall(args, z3::implies(non_neg_args_cond, use2z3(a))));
//     } else {
//         s.add(!use2z3(a));
//     }
// 
//     Value* v = a->get();
//     if (auto inst = dyn_cast_or_null<Instruction>(v)) {
//         s.add(all2z3(inst));
//         pc_type assert_pc = path_condition(inst->getParent());
//         s.add(assert_pc.first);
//         for (Use* u : assert_pc.second) {
//             Value* use_v = u->get();
//             auto inst_use = dyn_cast_or_null<Instruction>(use_v);
//             if (inst_use) s.add(all2z3(inst_use));
//         }
//     }
//     std::vector<rec_ty> closed;
//     for (Loop* loop : visited_loops) {
//         rec_ty recs = loop2rec(loop);
//         initial_ty initials = loop2initial(loop);
//         auto rec_s = rec_solver(z3ctx);
//         rec_s.set_eqs(recs);
//         rec_s.add_initial_values(initials.first, initials.second);
//         rec_s.solve();
//         z3::expr bnd = loop_bound(loop);
//         s.add(bnd);
//         z3::expr_vector ns(z3ctx);
//         z3::expr_vector Ns(z3ctx);
//         ns.push_back(z3ctx.int_const("n0"));
//         Ns.push_back(z3ctx.int_const(("N_" + std::to_string(loop2idx[loop]) + "_0").data()));
//         rec_ty res = rec_s.get_res();
//         if (!res.empty()) {
//             closed.push_back(res);
//             z3::expr ind_var = z3ctx.int_const("n0");
//             for (auto r : res) {
//                 z3::expr k = r.first;
//                 s.add(z3::forall(ind_var, z3::implies(ind_var >= 0, k == r.second)));
//                 s.add(k.substitute(ns, Ns) == r.second.substitute(ns, Ns));
//             }
//         }
//     }
//     z3::expr_vector axioms = s.assertions();
//     z3::expr_vector new_axioms(z3ctx);
//     z3::expr n = z3ctx.int_const("n0");
//     z3::expr free_var = z3ctx.variable(0, z3ctx.int_sort());
//     z3::expr_vector src(z3ctx);
//     z3::expr_vector dst(z3ctx);
//     src.push_back(n);
//     dst.push_back(free_var);
//     for (auto e : axioms) {
//         z3::expr cur_e = e;
//         for (rec_ty c : closed) {
//             for (auto p : c) {
//                 z3::func_decl f = p.first.decl();
//                 z3::expr closed_form = p.second.substitute(src, dst);
//                 z3::func_decl_vector fs(z3ctx);
//                 fs.push_back(f);
//                 z3::expr_vector closed_forms(z3ctx);
//                 closed_forms.push_back(closed_form);
//                 cur_e = cur_e.substitute(fs, closed_forms);
//             }
//         }
//         new_axioms.push_back(cur_e);
//     }
//     s.reset();
//     s.add(new_axioms);
//     std::string filename = "tmp/tmp" + std::to_string(out_idx) + ".smt2";
//     std::ofstream out(filename);
//     out << s.to_smt2().data() << "\n";
//     out.close();
//     auto val_res = s.check();
//     validation_type res = unknown;
//     switch (val_res) {
//         case z3::sat  : res = wrong  ; break;
//         case z3::unsat: res = correct; break;
//         default       : res = unknown; break;
//     }
//     return res;
// }

std::vector<path_ty> c2z3::get_paths_from_to(BasicBlock* from, BasicBlock* to) {
    std::vector<path_ty> res;
    LoopInfo& LI = LIs.at(main);
    Loop* to_loop = LI.getLoopFor(to);
    if (to_loop && to != to_loop->getHeader()) {
        return get_paths_from_to(from, to_loop->getHeader());
    }
    if (from == to) {
        res.push_back({from});
        return res;
    }
    for (auto bb = pred_begin(to); bb != pred_end(to); bb++) {
        BasicBlock* cur_bb = *bb;
        if (is_back_edge(cur_bb, to)) {
            // errs() << cur_bb->getName() << ' ' << to->getName() << "\n";
            continue;
        }
        Loop *loop = LI.getLoopFor(cur_bb);
        // if (loop) cur_bb =loop->getHeader();
        if (loop) cur_bb = loop->getOutermostLoop()->getHeader();
        auto prev_paths = get_paths_from_to(from, cur_bb);
        for (auto p : prev_paths) {
            p.push_back(to);
            res.push_back(p);
        }
    }
    return res;
}

std::vector<path_ty>
c2z3::get_paths_from_to_loop(Loop* loop) {
    BasicBlock* header = loop->getHeader();
    auto res = _get_paths_from_to_loop(loop, header, {});
    return res;
}

std::vector<path_ty>
c2z3::_get_paths_from_to_loop(Loop* loop, BasicBlock* cur_bb, std::vector<edge_ty> visited_edges) {
    BasicBlock* latch = loop->getLoopLatch();
    // for (auto edge : visited_edges) {
    //     errs() << edge.first->getName() << " " << edge.second->getName() << "\n";
    // }
    if (cur_bb == loop->getHeader() && visited_edges.size() != 0) {
        return {};
        // path_ty p;
        // p.push_back(cur_bb);
        // return {p};
    }
    std::vector<path_ty> res;
    for (auto succ : successors(cur_bb)) {
        if (!loop->contains(succ) || std::find(visited_edges.begin(), visited_edges.end(), std::make_pair(cur_bb, succ)) != visited_edges.end()) continue;
        std::vector<edge_ty> cur_visited = visited_edges;
        cur_visited.push_back(std::make_pair(cur_bb, succ));
        std::vector<path_ty> post_path = _get_paths_from_to_loop(loop, succ, cur_visited);
        if (post_path.size() == 0) {
            path_ty p = {cur_bb};
            res.push_back(p);
        } else {
            for (auto p : post_path) {
                p.insert(p.begin(), cur_bb);
                res.push_back(p);
            }
        }
    }
    return res;
}

bool
c2z3::is_back_edge_loop(Loop* loop, BasicBlock* from, BasicBlock* to) {
    return loop->getHeader() == to && loop->getLoopLatch() == from;
}

z3::func_decl c2z3::get_z3_function(Use* u) {
    Value* v = u->get();
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = LIs.at(main);
    int dim = LI.getLoopDepth(inst->getParent());
    return get_z3_function(v, dim);
}

bool c2z3::is_bool(Value* v) {
    Type* ty = v->getType();
    return ty->isIntegerTy() && ty->getIntegerBitWidth() == 1;
}

z3::func_decl c2z3::get_array_function(Value* v, MemoryAccess* access) {
    int arity = array_info.at(v).size();
    int m_id = get_m_phi_def_id(access);
    int dim = get_dim(access->getBlock());
    return get_array_function(v, m_id, arity + dim);
}

z3::func_decl c2z3::get_array_function(Value* v, int mem_id, int num_args) {
    std::string arr_name = get_array_name(v, mem_id);
    z3::sort_vector sorts = get_sorts(num_args);
    z3::sort ret_sort = z3ctx.int_sort();
    return z3ctx.function(arr_name.data(), sorts, ret_sort);
}

z3::func_decl c2z3::get_array_function(Value* v) {
    MemorySSA& MSSA = MSSAs.at(main);
    LoopInfo& LI = LIs.at(main);
    const char* var_name = nullptr;
    int dim = 0;
    int arity = 0;
    // if (auto store = dyn_cast_or_null<StoreInst>(v)) {
        array_access_ty access = get_array_access_from_load_store(v);
        // MemoryAccess* m_access = MSSA.getMemoryAccess(store);
        // auto m_access_def = dyn_cast_or_null<MemoryDef>(m_access);
        // MemoryAccess* m_access_use = m_access_def->getDefiningAccess();
        MemoryAccess* m_access_use = get_mem_use(v);
        int idx = get_m_phi_def_id(m_access_use);
        // BasicBlock* bb = get_bb_from_m_access(m_access_use);
        BasicBlock* bb = m_access_use->getBlock();
        // if (auto m_access_use_def = dyn_cast_or_null<MemoryDef>(m_access_use)) {
        //     idx = m_access_use_def->getID();
        //     bb = m_access_use_def->getBlock();
        // } else if (auto m_access_use_phi = dyn_cast_or_null<MemoryPhi>(m_access_use)) {
        //     idx = m_access_use_phi->getID();
        //     bb = m_access_use_phi->getBlock();
        // }
        // int idx = m_access_use_def->getID();
        dim = LI.getLoopDepth(bb);
        arity = array_info.at(access.first).size();
        var_name = (std::string(access.first->getName().data()) + "_" + std::to_string(idx)).data();
    // } else if (auto load = dyn_cast_or_null<LoadInst>(v)) {
    //     array_access_ty access = get_array_access_from_load_store(v);
    //     MemoryAccess* m_access_use = get_mem_use(v);
    //     int m_id = get_m_phi_def_id(m_access_use);
    // }
    z3::sort_vector args_sorts = get_sorts(dim + arity);
    z3::sort ret_sort = z3ctx.int_sort();
    return z3ctx.function(var_name, args_sorts, ret_sort);
}

z3::sort_vector c2z3::get_sorts(int num) {
    z3::sort_vector sorts(z3ctx);
    for (int i = 0; i < num; i++) {
        sorts.push_back(z3ctx.int_sort());
    }
    return sorts;
}

z3::func_decl c2z3::get_z3_function(Value* v, int dim) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    assert(inst);
    z3::sort ret_sort = is_bool(v) ? z3ctx.bool_sort() : z3ctx.int_sort();
    if (auto CI = dyn_cast_or_null<ZExtInst>(v)) {
        Value* op = CI->getOperand(0);
        if (is_bool(op)) ret_sort = z3ctx.bool_sort();
    }
    int arity = get_arity(v);
    const char* var_name = v->getName().data();
    array_access_ty access;
    MemorySSA& MSSA = MSSAs.at(main);
    if (auto store = dyn_cast_or_null<StoreInst>(v)) {
        MemoryAccess* m_access = MSSA.getMemoryAccess(inst);
        auto m_access_def = dyn_cast_or_null<MemoryDef>(m_access);
        assert(m_access_def);
        // auto m_access_use = m_access_def->getDefiningAccess();
        // auto m_access_use_cast = dyn_cast_or_null<MemoryDef>(m_access_use);
        access = get_array_access_from_load_store(v);
        int idx = m_access_def->getID();
        var_name = (std::string(access.first->getName().data()) + "_" + std::to_string(idx)).data();
    } else if (auto gep = dyn_cast_or_null<GetElementPtrInst>(v)) {
        access = get_array_access_from_gep(gep);
        return array_z3_func.at(access.first);
        // arity = array_info.at(access.first).size();
        // int idx = array_index[access.first];
        // var_name = (std::string(access.first->getName().data()) + "_" + std::to_string(idx)).data();
    } else if (auto alloc = dyn_cast_or_null<AllocaInst>(v)) {
        access.first = v;
        Value* sz = alloc->getArraySize();
        Type* ty = alloc->getAllocatedType();
        int num_e = 1;
        if (auto arr_ty = dyn_cast_or_null<ArrayType>(ty))
            num_e = arr_ty->getNumElements();
        z3::expr_vector arr_dim_info(z3ctx);
        arr_dim_info.push_back(v2z3(sz, dim, false) * num_e);
        array_info.insert_or_assign(inst, arr_dim_info);
        arity = array_info.at(inst).size();
        array_index[inst] = 0;
        array_def_block.insert_or_assign(inst, alloc->getParent());
    }

    z3::sort_vector args_sorts = get_sorts(dim + arity);
    z3::func_decl f = z3ctx.function(var_name, args_sorts, ret_sort);
    if (isa<StoreInst>(v) || isa<AllocaInst>(v)) {
        array_z3_func.insert_or_assign(access.first, f);
    }
    return f;
}

array_access_ty c2z3::get_array_access_from_load_store(Value* v) {
    Value* ptr = nullptr;
    assert(isa<LoadInst>(v) || isa<StoreInst>(v));
    if (auto CI = dyn_cast_or_null<LoadInst>(v)) {
        ptr = CI->getPointerOperand();
    } else if (auto CI = dyn_cast_or_null<StoreInst>(v)) {
        ptr = CI->getPointerOperand();
    }
    auto arr_ptr = dyn_cast_or_null<GetElementPtrInst>(ptr);
    array_access_ty arr_access_args = get_array_access_from_gep(arr_ptr);
    return arr_access_args;
}

array_access_ty c2z3::get_array_access_from_gep(GetElementPtrInst* gep) {
    Value* arr_ptr = gep->getPointerOperand();
    assert(isa<AllocaInst>(arr_ptr));
    std::vector<Use*> access_args;
    for (auto idx = gep->idx_begin() + 1; idx != gep->idx_end(); idx++) {
        // Value* idx_v = idx->get();
        access_args.push_back(idx);
    }
    return {arr_ptr, access_args};
}

z3::expr_vector c2z3::get_args(int dim, bool c, bool plus, bool prefix, Loop* loop) {
    z3::expr_vector args(z3ctx);
    // const char* idx_prefix = c ? "N" : "n";
    std::string idx_prefix = "n";
    if (c && loop) {
        idx_prefix = "N_" + std::to_string(loop2idx.at(loop)) + "_";
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

// pc_type c2z3::loop_condition(Loop* loop) {
//     BasicBlock* header = loop->getHeader();
//     BasicBlock* latch = loop->getLoopLatch();
//     Instruction* term = loop->getLoopLatch()->getTerminator();
//     bool is_negated = false;
//     Use* cond = nullptr;
//     if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
//         if (CI->isConditional()) {
//             is_negated = CI->getSuccessor(1) == header;
//             cond = &CI->getOperandUse(0);
//         }
//     }
//     z3::expr piece = use2z3(cond);
//     // z3::func_decl cond_func = get_z3_function(cond);
//     // z3::expr_vector loop_args = get_args(cond_func.arity());
//     // z3::expr piece = cond_func(loop_args);
// 
//     pc_type local_pc = path_condition_from_to(header, latch);
//     piece = is_negated ? !piece : piece;
//     piece = piece && local_pc.first;
//     LoopInfo& LI = LIs.at(main);
//     int dim = LI.getLoopDepth(header);
//     z3::expr_vector ns(z3ctx);
//     z3::expr_vector n1s(z3ctx);
//     z3::expr_vector Ns(z3ctx);
//     z3::expr premises = z3ctx.bool_val(true);
//     z3::expr cons_N = z3ctx.bool_val(true);
//     for (int i = 0; i < dim; i++) {
//         std::string idx = "n" + std::to_string(i);
//         ns.push_back(z3ctx.int_const(idx.data()));
//         n1s.push_back(1 + z3ctx.int_const(idx.data()));
//         idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(i);
//         Ns.push_back(z3ctx.int_const(idx.data()));
//         premises = premises && ns.back() < Ns.back();
//         cons_N = cons_N && Ns.back() >= 0;
//     }
//     piece = piece.substitute(n1s, ns);
//     z3::expr loop_cond = z3::forall(ns, z3::implies(premises, piece));
//     z3::expr exit_cond = !piece.substitute(ns, Ns);
//     z3::expr res = loop_cond && cons_N && exit_cond;
//     // z3::expr res = cons_N && exit_cond;
//     // res = res && loop_cond && exit_cond;
//     // res = res && local_pc.first;
//     local_pc.second.insert(cond);
//     // return res;
//     return {res, local_pc.second};
// }

// z3::expr c2z3::path_condition_header2bb(BasicBlock* bb) {
//     LoopInfo& LI = LIs.at(main);
//     Loop* loop = LI.getLoopFor(bb);
//     BasicBlock* header = &main->getEntryBlock();
//     if (loop) header = loop->getHeader();
//     for (BasicBlock* prev_bb : predecessors(bb)) {
//         Loop* prev_loop = LI.getLoopFor(prev_bb);
//         z3::expr prev_cond = path_condition_header2bb(bb);
//         if (prev_loop == loop) {
//         }
//     }
// }

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

z3::expr c2z3::loop_bound(Loop* loop, rec_solver& rec_s) {
    closed_form_ty closed = rec_s.get_res();
    for (auto pair : closed) {
        if (!pair.first.is_const()) {
            return z3ctx.bool_val(true);
        }
    }
    BasicBlock* header = loop->getHeader();
    BasicBlock* latch = loop->getLoopLatch();
    Instruction* term = latch->getTerminator();
    bool is_negated = false;
    Value* cond = nullptr;
    if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
        if (CI->isConditional()) {
            is_negated = CI->getSuccessor(1) == header;
            cond = CI->getOperand(0);
        }
    }
    z3::expr piece = cond ? v2z3(cond) : z3ctx.bool_val(true);

    pc_type local_pc = path_condition_from_to(header, latch);
    std::set<Value*> all_used = local_pc.second;
    std::set<PHINode*> all_phis;
    if (cond) all_used.insert(cond);

    rec_ty loop_recs = loop2rec(loop);
    initial_ty loop_initials = loop2initial(loop);
    // auto rec_s = rec_solver(z3ctx);
    // rec_s.set_eqs(loop_recs);
    // rec_s.add_initial_values(loop_initials.first, loop_initials.second);
    // rec_s.solve();
    z3::expr ind_var = rec_s.get_ind_var();
    z3::expr loop_bnd = z3ctx.int_const("N0");

    piece = is_negated ? !piece : piece;
    piece = piece && local_pc.first;
    LoopInfo& LI = LIs.at(main);
    // int dim = LI.getLoopDepth(header);
    z3::expr_vector ns(z3ctx);
    // z3::expr_vector n1s(z3ctx);
    z3::expr_vector Ns(z3ctx);
    ns.push_back(ind_var);
    Ns.push_back(loop_bnd);
    // z3::expr_vector N1s(z3ctx);
    // z3::expr premises = z3ctx.bool_val(true);
    // z3::expr cons_N = z3ctx.bool_val(true);
    // for (int i = 0; i < dim; i++) {
    //     std::string idx = "n" + std::to_string(i);
    //     ns.push_back(z3ctx.int_const(idx.data()));
    //     n1s.push_back(1 + z3ctx.int_const(idx.data()));
    //     idx = "N_" + std::to_string(loop2idx[loop]) + "_" + std::to_string(i);
    //     Ns.push_back(z3ctx.int_const(idx.data()));
    //     N1s.push_back(z3ctx.int_const(idx.data()) - 1);
    z3::expr premises = ns.back() < Ns.back() && ns.back() >= 0;
    z3::expr cons_N = Ns.back() >= 0;
    //     cons_N = cons_N && Ns.back() >= 0;
    // }
    // piece = piece.substitute(n1s, ns);

    for (Value* u : all_used) {
        // z3::expr loop_expr = loop_expression(u);
        z3::expr loop_expr = express_v_as_header_phis(u);
        z3::expr_vector src(z3ctx);
        z3::expr_vector dst(z3ctx);
        src.push_back(v2z3(u));
        dst.push_back(loop_expr);
        // loop_cond = loop_cond.substitute(src, dst);
        piece = piece.substitute(src, dst);
        // std::set<PHINode*> local_phis = get_header_defs(u);
        // all_phis.insert(local_phis.begin(), local_phis.end());
    }
    z3::expr_vector src(z3ctx);
    z3::expr_vector dst(z3ctx);
    for (auto r : closed) {
        src.push_back(r.first);
        dst.push_back(r.second);
    }
    z3::expr final_res = z3ctx.bool_val(true);
    piece = piece.substitute(src, dst);
    z3::expr loop_cond = z3::forall(ns, z3::implies(premises, piece));
    z3::expr exit_cond = !piece.substitute(ns, Ns);
    z3::expr res = loop_cond && cons_N && exit_cond;
    z3::tactic t = z3::tactic(z3ctx, "qe"); // & z3::tactic(z3ctx, "ctx-solver-simplify");
    z3::goal g(z3ctx);
    // if (loop->isRotatedForm())
    //     g.add(res.substitute(Ns, N1s));
    // else
    g.add(res);
    auto r = t.apply(g);
    for (int i = 0; i < r.size(); i++) {
        z3::expr cur_expr = r[i].as_expr();
        std::string cur_expr_string = cur_expr.to_string();
        if (cur_expr_string.find("exists") != std::string::npos) {
            return z3ctx.bool_val(true);
        }
        final_res = final_res && r[i].as_expr();
    }
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
        res.first = res.first && qq[i].as_expr();
    }
    return res;
}

pc_type c2z3::pc_and(const pc_type& a, const pc_type& b) {
    z3::expr cond = a.first && b.first;
    std::set<Value*> use_set;
    std::set_union(a.second.begin(), a.second.end(),
                   b.second.begin(), b.second.end(),
                   std::inserter(use_set, use_set.end()));
    return {cond, use_set};
}

pc_type c2z3::pc_or(const pc_type& a, const pc_type& b) {
    z3::expr cond = a.first || b.first;
    std::set<Value*> use_set;
    std::set_union(a.second.begin(), a.second.end(),
                   b.second.begin(), b.second.end(),
                   std::inserter(use_set, use_set.end()));
    return {cond, use_set};
}

bool c2z3::is_back_edge(BasicBlock* from, BasicBlock* to) {
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(to);
    bool res = loop && loop->contains(from) && loop->isLoopLatch(from) && loop->getHeader() == to;
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
            Value* u = CI->getOperand(0);
            res.first = v2z3(u);
            res.second.insert(u);
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
