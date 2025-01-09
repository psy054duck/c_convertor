#include "value2z3.h"
#include <stdexcept>
#include <algorithm>
#include <iterator>
#include <numeric>
#include "boost/algorithm/string.hpp"

using namespace llvm;

value2z3::value2z3(Function *F, z3::context& _z3ctx): F(F), z3ctx(_z3ctx) {
    PassBuilder PB;
    PB.registerLoopAnalyses(LA);
    PB.registerFunctionAnalyses(FAM);
}

z3::expr_vector
value2z3::inst2z3(Instruction* inst, BasicBlock* prev_bb) {
    z3::expr_vector res(z3ctx);
    if (auto CI = dyn_cast_or_null<CallInst>(inst)) {
        return res;
    }
    Type* tp = inst->getType();
    const char* var_name = inst->getName().data();
    bool is_bool = tp->isIntegerTy(1);
    BasicBlock* block = inst->getParent();
    z3::expr_vector initial_res(z3ctx);
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
            errs() << opcode << "\n";
            exit(-1);
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
            errs() << opcode << "\n";
            exit(-1);
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
        if (called_name.ends_with("uint")) {
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
        }
    } else if (auto CI = dyn_cast_or_null<SExtInst>(inst)) {
        res.push_back(f(args) == v2z3(CI->getOperand(0)));
    } else if (auto CI = dyn_cast_or_null<ZExtInst>(inst)) {
        res.push_back(f(args) == v2z3(CI->getOperand(0)));
    } else if (auto CI = dyn_cast_or_null<TruncInst>(inst)) {
        res.push_back(f(args) == v2z3(CI->getOperand(0)));
    } else if (auto CI = dyn_cast_or_null<GetElementPtrInst>(inst)) {

    } else {
        errs() << opcode << "\n";
        exit(-1);
    }
    return res;
}

z3::expr
value2z3::v2z3(Value* v, int dim, int plus) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        IntegerType* i_type = CI->getIntegerType();
        bool is_bool = i_type->isIntegerTy(1);
        if (is_bool)
            return z3ctx.bool_val(CI->getZExtValue());
        else
            return z3ctx.int_val(CI->getSExtValue());
    }
    z3::func_decl f = get_z3_function(v, dim);
    z3::expr_vector args = get_args(dim, false, plus, true);
    // z3::expr_vector arr_args = get_access_index(v);
    // combine_vec(arr_args, args);
    return f(args);
}

z3::func_decl
value2z3::get_z3_function(Value* v, int dim) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    // assert(inst);
    z3::sort ret_sort = is_bool(v) ? z3ctx.bool_sort() : z3ctx.int_sort();
    if (auto CI = dyn_cast_or_null<ZExtInst>(v)) {
        Value* op = CI->getOperand(0);
        if (is_bool(op)) ret_sort = z3ctx.bool_sort();
    }
    std::string var_name = v->getName().str();
    z3::sort_vector args_sorts = get_sorts(dim);
    boost::replace_all(var_name, ".", "_");
    z3::func_decl f = z3ctx.function(("s" + var_name).data(), args_sorts, ret_sort);
    return f;
}

z3::func_decl
value2z3::get_z3_function(Use* u) {
    Value* v = u->get();
    auto inst = dyn_cast_or_null<Instruction>(v);
    LoopInfo& LI = FAM.getResult<LoopAnalysis>(*F);
    int dim = LI.getLoopDepth(inst->getParent());
    return get_z3_function(v, dim);
}

z3::expr
value2z3::get_z3_formal_application(Function* f) {
    z3::func_decl f_decl = get_z3_function(f);
    z3::expr_vector args = get_z3_formal_parameters(f);
    return f_decl(args);
}

z3::expr_vector
value2z3::get_z3_formal_parameters(Function* f) {
    z3::expr_vector args(z3ctx);
    for (auto& arg : f->args()) {
        args.push_back(v2z3(&arg));
    }
    return args;
}

z3::expr_vector
value2z3::get_args(int dim, bool c, bool plus, bool prefix, Loop* loop) {
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

z3::expr
value2z3::use2z3(Use* u) {
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

    auto CI = dyn_cast<Instruction>(use_def);
    LoopInfo& LI = FAM.getResult<LoopAnalysis>(*F);
    int dim = LI.getLoopDepth(CI->getParent());

    z3::func_decl f = get_z3_function(u);

    Value* user = u->getUser();
    auto user_inst = dyn_cast<Instruction>(user);
    BasicBlock* user_block = user_inst->getParent();
    BasicBlock* def_block = CI->getParent();
    Loop* user_loop = LI.getLoopFor(user_block);
    Loop* def_loop = LI.getLoopFor(def_block);

    z3::expr_vector args = get_args(dim, false, true, false);
    if (is_header_phi(use_def, def_loop)) {
        args = get_args(dim, false, false, false);
    }
    bool is_n = false;
    if (def_loop && def_loop->contains(user_inst)) {
    } else if (def_loop) {
        args.pop_back();
        std::string idx = "N_" + std::to_string(loop2idx[def_loop]) + "_" + std::to_string(dim - 1);
        args.push_back(z3ctx.int_const(idx.data()));
    }
    // z3::func_decl f = z3ctx.function(var_name, params, ret_sort);
    return f(args);
}

bool
value2z3::is_bool(Value* v) {
    Type* ty = v->getType();
    return ty->isIntegerTy() && ty->getIntegerBitWidth() == 1;
}

bool
value2z3::is_header_phi(Value* v, Loop* loop) {
    auto inst = dyn_cast_or_null<Instruction>(v);
    if (!inst || !loop) return false;
    BasicBlock* bb = inst->getParent();
    BasicBlock* header = loop->getHeader();
    return bb == header && isa<PHINode>(v);
}

void
value2z3::get_loop_idx() {
    int i = 1;
    LoopInfo& LI = FAM.getResult<LoopAnalysis>(*F);
    for (Loop* loop : LI.getLoopsInPreorder()) {
        loop2idx.insert_or_assign(loop, i++);
    }
}

z3::sort_vector
value2z3::get_sorts(int num) {
    z3::sort_vector sorts(z3ctx);
    for (int i = 0; i < num; i++) {
        sorts.push_back(z3ctx.int_sort());
    }
    return sorts;
}

bool
value2z3::is_parameter(Value* v) {
    for (auto& arg : F->args()) {
        if (&arg == v) {
            return true;
        }
    }
    return false;
}

z3::expr
value2z3::express_v_as_inputs(Value* v, int dim, path_ty& path) {
    if (auto CI = dyn_cast_or_null<ConstantInt>(v)) {
        int svalue = CI->getSExtValue();
        return is_bool(v) ? z3ctx.bool_val(svalue) : z3ctx.int_val(svalue);
    }

    if (isa<UndefValue>(v)) {
        // an undef means the path is infeasible, so any value can be used.
        return z3ctx.int_val(0);
    }

    if (is_parameter(v)) {
        return v2z3(v, 0);
    }

    auto inst = dyn_cast_or_null<Instruction>(v);
    BasicBlock* bb = inst->getParent();
    z3::func_decl f = get_z3_function(v, dim);
    z3::expr_vector args = get_args(dim, false, false, false);
    z3::expr_vector res(z3ctx);
    int opcode = inst->getOpcode();
    if (inst->isBinaryOp()) {
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = express_v_as_inputs(op0, dim, path);
        z3::expr z3op1 = express_v_as_inputs(op1, dim, path);
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
            errs() << opcode << "\n";
            exit(-1);
        }
    } else if (opcode == Instruction::ICmp) {
        auto CI = dyn_cast<ICmpInst>(inst);
        auto pred = CI->getPredicate();
        Value* op0 = inst->getOperand(0);
        Value* op1 = inst->getOperand(1);
        z3::expr z3op0 = express_v_as_inputs(op0, dim, path);
        z3::expr z3op1 = express_v_as_inputs(op1, dim, path);
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
            errs() << opcode << "\n";
            exit(-1);
        }
    } else if (auto CI = dyn_cast_or_null<SelectInst>(inst)) {
        z3::expr cond = express_v_as_inputs(CI->getOperand(0), dim, path);
        z3::expr first = express_v_as_inputs(CI->getOperand(1), dim, path);
        z3::expr second = express_v_as_inputs(CI->getOperand(2), dim, path);
        return z3::ite(cond, first, second);
    } else if (auto call = dyn_cast_or_null<CallInst>(inst)) {
        // return z3ctx.int_const("unknown");
        Function* f = call->getFunction();
        z3::func_decl f_decl = get_z3_function(f);
        z3::expr_vector args_z3(z3ctx);
        for (auto& arg : call->args()) {
            args_z3.push_back(express_v_as_inputs(arg.get(), dim, path));
        }
        return f_decl(args_z3);
    } else if (auto CI = dyn_cast_or_null<PHINode>(inst)) {
        if (auto phi = dyn_cast_or_null<PHINode>(v)) {
            BasicBlock* cur_bb = phi->getParent();
            int bb_idx = find_bb(cur_bb, path);
            BasicBlock* prev_bb = path[bb_idx - 1];
            Value* instantiated_v = phi->getIncomingValueForBlock(prev_bb);
            return express_v_as_inputs(instantiated_v, dim, path);
        }

    } else if (auto CI = dyn_cast_or_null<SExtInst>(inst)) {
        return express_v_as_inputs(CI->getOperand(0), dim, path);
    } else if (auto CI = dyn_cast_or_null<ZExtInst>(inst)) {
        return express_v_as_inputs(CI->getOperand(0), dim, path);
    } else if (auto call = dyn_cast_or_null<CallInst>(inst)) {
        return v2z3(v, dim);
    } else {
        errs() << opcode << "\n";
        exit(-1);
    }
}

z3::func_decl
value2z3::get_z3_function(Function* f, int arity) {
    int dim = arity;
    if (arity == -1)
        dim = f->arg_size();
    z3::sort ret_sort = z3ctx.int_sort();
    std::string var_name = f->getName().str();
    z3::sort_vector args_sorts = get_sorts(dim);
    boost::replace_all(var_name, ".", "_");
    z3::func_decl f_decl = z3ctx.function(("s" + var_name).data(), args_sorts, ret_sort);
    return f_decl;
}