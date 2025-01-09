#include "function_summary.h"

using namespace llvm;

function_summary::function_summary(Function* F, z3::context& _z3ctx): F(F), llvm2z3(F, _z3ctx), rec_s(llvm2z3.get_context()) {
    LoopAnalysisManager LAM;
    FunctionAnalysisManager FAM;
    PassBuilder PB = PassBuilder();
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);

    LoopInfo& LI = FAM.getResult<LoopAnalysis>(*F);
    assert(LI.empty());
}

// function_summary::function_summary(const function_summary& other): F(other.F) {}
// function_summary
// function_summary::operator=(const function_summary& other) {
//     // converter = other.converter;
//     F = other.F;
// }

std::vector<ReturnInst*>
function_summary::get_all_ret_inst() {
    std::vector<ReturnInst*> res;
    for (BasicBlock& bb : *F) {
        for (Instruction& inst : bb) {
            auto ret = dyn_cast_or_null<ReturnInst>(&inst);
            if (ret) {
                res.push_back(ret);
            }
        }
    }
    return res;
}

void
function_summary::summarize() {
    std::vector<path_ty> paths = get_all_paths();
    std::vector<z3::expr> conds;
    std::vector<rec_ty> exprs;
    z3::expr func = llvm2z3.get_z3_formal_application(F);
    for (auto path : paths) {
        if (!is_feasible(path)) continue;
        z3::expr cond = get_path_condition(path);
        ReturnInst* ret = get_ret(path);
        Value* ret_v = ret->getOperand(0);
        z3::expr expr = llvm2z3.express_v_as_inputs(ret_v, 0, path);
        conds.push_back(cond);
        rec_ty statement = {{func, expr}};
        exprs.push_back(statement);
    }
    rec_s.set_eqs(conds, exprs);
    rec_s.solve();
    closed_form_ty closed = rec_s.get_res();
    summary = closed.at(llvm2z3.get_z3_function(F, 0)());
}

std::optional<z3::expr>
function_summary::get_summary() {
    if (!summary.has_value()) {
            summarize();
        // try {
        // } catch (...) {

        // }
    }
    return summary;
}

bool
function_summary::is_feasible(path_ty& path) {
    z3::expr cond = get_path_condition(path);
    z3::solver solver(llvm2z3.get_context());
    solver.add(cond);
    auto res = solver.check();
    if (res == z3::unsat) {
        return false;
    }
    return true;
}

ReturnInst*
function_summary::get_ret(path_ty& path) {
    BasicBlock* exit_bb = path.back();
    Value* v = exit_bb->getTerminator();
    ReturnInst* ret = dyn_cast_or_null<ReturnInst>(v);
    return ret;
}

std::vector<path_ty>
function_summary::get_all_paths() {
    std::vector<ReturnInst*> all_rets = get_all_ret_inst();
    BasicBlock& entry_bb = F->getEntryBlock();
    std::vector<path_ty> res;
    for (auto ret : all_rets) {
        BasicBlock* exit_bb = ret->getParent();
        std::vector<path_ty> paths = get_path_from_to(&entry_bb, exit_bb);
        res.insert(res.end(), paths.begin(), paths.end());
    }
    return res;
}

std::vector<path_ty>
function_summary::get_path_from_to(BasicBlock* from, BasicBlock* to) {
    path_ty cur_path;
    std::vector<path_ty> res = _get_path_from_to(from, to, cur_path);
    return res;
}

std::vector<path_ty>
function_summary::_get_path_from_to(BasicBlock* from, BasicBlock* to, path_ty& cur_path)  {
    cur_path.push_back(from);
    std::vector<path_ty> res;
    if (from == to) {
        res.push_back(cur_path);
        cur_path.pop_back();
        return res;
    }
    for (BasicBlock* bb : successors(from)) {
        std::vector<path_ty> tmp = _get_path_from_to(bb, to, cur_path);
        res.insert(res.end(), tmp.begin(), tmp.end());
    }
    cur_path.pop_back();
    return res;
}

z3::expr
function_summary::get_path_condition(path_ty& path) {
    z3::expr res = llvm2z3.get_context().bool_val(true);
    int sz = path.size();
    for (int i = 0; i < sz - 1; i++) {
        Instruction* term = path[i]->getTerminator();
        BranchInst* br = dyn_cast_or_null<BranchInst>(term);
        if (br && br->isConditional()) {
            Value* cond = br->getCondition();
            if (br->getSuccessor(0) == path[i + 1]) {
                res = res && llvm2z3.express_v_as_inputs(cond, 0, path);
            } else {
                res = res && !llvm2z3.express_v_as_inputs(cond, 0, path);
            }
        }
    }
    return res.simplify();
}
