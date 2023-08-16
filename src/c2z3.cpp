#include "c2z3.h"
#include <stdexcept>

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

c2z3::c2z3(std::unique_ptr<Module> &mod): m(std::move(mod)) {
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
    MPM.run(*m, MAM);


    std::error_code ec;
    raw_fd_ostream output_fd("tmp/tmp.ll", ec);
    m->print(output_fd, NULL);
    output_fd.close();
    z3::context z3ctx;
    auto &fam = MAM.getResult<FunctionAnalysisManagerModuleProxy>(*m).getManager();
    for (auto F = m->begin(); F != m->end(); F++) {
        if (!F->isDeclaration()) {
            LoopInfo& LI = fam.getResult<LoopAnalysis>(*F);
            DominatorTree DT = DominatorTree(*F);
            PostDominatorTree PDT = PostDominatorTree(*F);
            // LIs[&*F] = LI;
            LIs.emplace(&*F, LI);
            DTs.emplace(&*F, DominatorTree(*F));
            PDTs.emplace(&*F, PostDominatorTree(*F));
            if (F->getName() == "main") {
                main = &*F;
            }
        }
    }
}

use_vector c2z3::getAllAssertions() {
    use_vector res;
    for (auto& bb : *main) {
        for (auto& ins : bb) {
            if (auto call = dyn_cast<CallInst>(&ins)) {
                Function* f = call->getCalledFunction();
                if (f->getName().endswith("assert")) {
                    assert(call->arg_size() == 1);
                    res.push_back(&call->getArgOperandUse(0));
                }
            }
        }
    }
    return res;
}

z3::expr_vector c2z3::inst2z3(Instruction* inst) {
    Type* tp = inst->getType();
    const char* var_name = inst->getName().data();
    bool is_bool = tp->isIntegerTy(1);
    z3::expr_vector res(z3ctx);
    LoopInfo& LI = LIs.at(main);
    BasicBlock* block = inst->getParent();
    Loop* loop = LI.getLoopFor(block);
    int dim = LI.getLoopDepth(block);
    z3::sort_vector params(z3ctx);
    z3::sort ret_sort = is_bool ? z3ctx.bool_sort() : z3ctx.int_sort();
    z3::expr_vector args(z3ctx);
    for (int i = 0; i < dim - 1; i++) {
        std::string idx = "n" + std::to_string(i);
        params.push_back(z3ctx.int_sort());
        args.push_back(z3ctx.int_const(idx.data()));
    }
    if (dim > 0) {
        std::string idx = "n" + std::to_string(dim - 1);
        params.push_back(z3ctx.int_sort());
        args.push_back(z3ctx.int_const(idx.data()) + 1);
    }
    z3::func_decl f = z3ctx.function(var_name, params, ret_sort);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
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
        } else {
            throw UnimplementedOperationException(opcode);
        }
    } else if (opcode == Instruction::ICmp) {
        auto CI = dyn_cast<ICmpInst>(inst);
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
    } else if (auto CI = dyn_cast<PHINode>(inst)) {
        for (int i = 0; i < CI->getNumIncomingValues(); i++) {
            BasicBlock* cur_bb = inst->getParent();
            BasicBlock* in_bb = CI->getIncomingBlock(i);
            Use* op = &CI->getOperandUse(i);
            z3::expr z3_op = use2z3(op);
            // phi in header
            if (loop && loop->getHeader() == block) {
                std::string n_idx = "n" + std::to_string(dim - 1);
                std::string N_idx = "N" + std::to_string(dim - 1);
                z3::expr z3_nidx = z3ctx.int_const(n_idx.data());
                z3::expr z3_Nidx = z3ctx.int_const(N_idx.data());
                if (!loop->contains(in_bb)) {
                    // initial
                    // args[dim - 1] = z3ctx.int_val(0);
                    args.pop_back();
                    args.push_back(z3ctx.int_val(0));
                    res.push_back(f(args) == z3_op);
                } else if (loop->getLoopLatch() == in_bb) {
                    // inductive
                    args.pop_back();
                    args.push_back(z3_nidx + 1);
                    // args[dim - 1] = z3_nidx + 1;
                    res.push_back(z3::implies(z3_nidx > 0, f(args) == z3_op));
                } else {
                    throw UnimplementedOperationException(opcode);
                }
            } else {
                z3::expr cond = path_condition(in_bb);
                // z3::expr local_cond = path_condition_b2b(in_bb, cur_bb);
                auto cond_negated = path_condition_b2b(in_bb, cur_bb);
                z3::expr local_cond = use2z3(cond_negated.first);
                Loop* prev_loop = LI.getLoopFor(in_bb);
                if (prev_loop && prev_loop->contains(cur_bb)) {
                    local_cond = cond_negated.second ? !local_cond : local_cond;
                } else {
                    local_cond = z3ctx.bool_val(true);
                }
                res.push_back(z3::implies(cond && local_cond, f(args) == z3_op));
            }
        }
    } else {
        throw UnimplementedOperationException(opcode);
    }
    return res;
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
    z3::sort_vector params(z3ctx);
    z3::expr_vector args(z3ctx);
    z3::sort ret_sort = is_bool ? z3ctx.bool_sort() : z3ctx.int_sort();

    for (int i = 0; i < dim; i++) {
        std::string idx = "n" + std::to_string(i);
        params.push_back(z3ctx.int_sort());
        args.push_back(z3ctx.int_const(idx.data()));
    }
    Value* user = u->getUser();
    auto user_inst = dyn_cast<Instruction>(user);
    BasicBlock* user_block = user_inst->getParent();
    BasicBlock* def_block = CI->getParent();
    Loop* user_loop = LI.getLoopFor(user_block);
    Loop* def_loop = LI.getLoopFor(def_block);
    bool is_n = false;
    if (def_loop->contains(user_inst)) {
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
        if (!is_n) {
            try {
                if (user_loop) {
                    args.pop_back();
                    std::string idx = "n" + std::to_string(dim - 1);
                    args.push_back(z3ctx.int_const(idx.data()) + 1);
                    // args[loop->getLoopDepth() - 1] = args[loop->getLoopDepth() - 1] + 1;
                }
            } catch (...) {

            }
        }
    } else {
        args.pop_back();
        std::string idx = "N" + std::to_string(dim - 1);
        args.push_back(z3ctx.int_const(idx.data()));
    }
    z3::func_decl f = z3ctx.function(var_name, params, ret_sort);
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

z3::expr_vector c2z3::all2z3(Instruction* inst) {
    if (visited_inst.contains(inst)) {
        return z3::expr_vector(z3ctx);
    }
    visited_inst.insert(inst);
    z3::expr_vector res = inst2z3(inst);
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
    return res;
}

z3::expr c2z3::path_condition(BasicBlock* bb) {
    if (path_conditions.find(bb) != path_conditions.end()) {
        return path_conditions.at(bb);
    }
    z3::expr res = z3ctx.bool_val(false);
    BasicBlock* entry = &main->getEntryBlock();
    if (bb == entry) {
        return z3ctx.bool_val(true);
    }
    LoopInfo& LI = LIs.at(main);
    Loop* loop = LI.getLoopFor(bb);
    for (BasicBlock* prev_bb : predecessors(bb)) {
        if (loop && bb == loop->getHeader() && loop->getLoopLatch() == prev_bb) continue;
        Instruction* term = prev_bb->getTerminator();
        z3::expr cur_cond_z3 = path_condition(prev_bb);
        // z3::expr local_path_cond = path_condition_b2b(prev_bb, bb);
        auto local_cond_negated = path_condition_b2b(prev_bb, bb);
        z3::expr local_path_cond = use2z3(local_cond_negated.first);
        local_path_cond = local_cond_negated.second ? !local_path_cond : local_path_cond;
        res = res || (cur_cond_z3 && local_path_cond);
    }
    res = res.simplify();
    path_conditions.insert_or_assign(bb, res);
    return res;
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

validation_type c2z3::check_assert(Use* a) {
    visited_inst.clear();
    z3::solver s(z3ctx);
    s.add(!use2z3(a));
    Value* v = a->get();
    if (auto inst = dyn_cast<Instruction>(v)) {
        s.add(all2z3(inst));
    }
    errs() << s.to_smt2().data() << "\n";
    auto val_res = s.check();
    validation_type res = unknown;
    switch (val_res) {
        case z3::sat  : res = wrong  ; break;
        case z3::unsat: res = correct; break;
        default       : res = unknown; break;
    }
    return res;
}

z3::expr c2z3::loop_condition(Loop* loop) {
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
    z3::expr res = use2z3(cond);
    res = is_negated ? !res : res;
    res = res && simple_path_condition_from_to(header, latch);
    return res;
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

pc_type c2z3::path_condition_from_to(BasicBlock* from, BasicBlock* to) {
    if (from == to) return {std::make_pair(nullptr, true)};
    std::vector<std::pair<Use*, bool>> res;
    LoopInfo& LI = LIs.at(main);
    Loop* to_loop = LI.getLoopFor(to);
    for (BasicBlock* prev_bb : predecessors(to)) {
        Loop* prev_loop = LI.getLoopFor(prev_bb);
        auto prev_path_condition = path_condition_from_to(from, prev_bb);
        if (prev_loop == to_loop) {

        }
    }
}

pc_type c2z3::path_condition_from_to_straight(BasicBlock* from, BasicBlock* to) {
    if (from == to) return {std::make_pair(nullptr, true)};
    for (BasicBlock* prev_bb : predecessors(to)) {
        pc_type prev_pc = path_condition_from_to_straight(from, prev_bb);
        std::pair<Use*, bool> local_pc = {nullptr, true};
        Instruction* term = from->getTerminator();
        if (auto CI = dyn_cast_or_null<BranchInst>(term)) {
            if (CI->isConditional()) {
                Use* cond = &CI->getOperandUse(0);
                bool is_positive = CI->getSuccessor(0) == to;
                local_pc = {cond, is_positive};
            }
        }
    }
}


void c2z3::test_loop_condition() {
    for (Loop* loop : LIs.at(main).getLoopsInPreorder()) {
        errs() << loop_condition(loop).simplify().to_string() << "\n";
    }
}