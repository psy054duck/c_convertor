#ifndef FUNCTION_SUMMARY
#define FUNCTION_SUMMARY

#include <vector>
#include <optional>

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/InstIterator.h"

#include "z3++.h"

#include "rec_solver.h"
#include "value2z3.h"
#include "structures.h"
// #include "c2z3.h"

using namespace llvm;

class function_summary {
    public:
        // function_summary(): F(nullptr), llvm2z3(F), rec_s(llvm2z3.get_context()) {}
        function_summary() = delete;
        function_summary(Function* F, z3::context& _z3ctx);
        // function_summary(const function_summary& other);
        // function_summary operator=(const function_summary& other);
        std::optional<z3::expr> get_summary();
    private:
        // c2z3 converter;
        Function* F;
        value2z3 llvm2z3;
        rec_solver rec_s;
        std::optional<z3::expr> summary;
        void summarize();
        std::vector<path_ty> get_all_paths();
        std::vector<ReturnInst*> get_all_ret_inst();
        std::vector<path_ty> get_path_from_to(BasicBlock* from, BasicBlock* to);
        std::vector<path_ty> _get_path_from_to(BasicBlock* from, BasicBlock* to, path_ty& cur_path);
        z3::expr get_path_condition(path_ty& path);
        ReturnInst* get_ret(path_ty& path);
        bool is_feasible(path_ty& path);

        // z3::expr express_as_input_values(Value* v, path_ty& path);
};

#endif