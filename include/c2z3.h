#ifndef C2Z3_H
#define C2Z3_H

#include "llvm/IRReader/IRReader.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LCSSA.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/InstructionNamer.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "z3++.h"

#include <string>
#include <vector>
#include <map>
#include <set>
#include <fstream>

#include "rec_solver.h"

using namespace llvm;
typedef std::vector<Use*> use_vector;
typedef std::vector<Value*> value_vector;
typedef std::pair<z3::expr, std::set<Use*>> pc_type;
typedef enum {
    correct,
    wrong,
    unknown
} validation_type;


std::string get_validation_type_name(validation_type ty);
void combine_vec(z3::expr_vector& v1, z3::expr_vector& v2);

class c2z3 {
    public:
        c2z3(std::unique_ptr<Module> &mod);
        use_vector getAllAssertions();
        validation_type check_assert(Use* a, int out_idx);
        z3::expr_vector inst2z3(Instruction* inst);
        z3::expr_vector all2z3(Instruction* inst);
        z3::expr use2z3(Use* u);
        z3::expr v2z3(Value* v, int dim, int plus);
        std::pair<Use*, bool> path_condition_b2b(BasicBlock* from, BasicBlock* to);
        std::set<Use*> get_bb_conditions(BasicBlock* bb);
        z3::expr path_condition_header2bb(BasicBlock* bb);
        z3::expr simple_path_condition_from_to(BasicBlock* from, BasicBlock* to);

        pc_type loop_condition(Loop* loop);

        int get_dim(Use* u);

        pc_type path_condition(BasicBlock* bb);
        pc_type path_condition_from_to(BasicBlock* from, BasicBlock* to);
        pc_type path_condition_from_to_straight(BasicBlock* from, BasicBlock* to);
        pc_type pc_and(const pc_type& a, const pc_type& b);
        pc_type pc_or(const pc_type& a, const pc_type& b);

        z3::expr express_v_as_header_phis(Value* v);
        z3::expr _express_v_as_header_phis(Value* v, Loop* inner_loop);

        z3::func_decl get_z3_function(Value* v, int dim);
        z3::func_decl get_z3_function(Use* u);
        z3::expr_vector get_args(int dim, bool c, bool plus, bool prefix, Loop* loop=nullptr);
        z3::expr_vector get_pure_args(int dim, bool c);
        z3::expr get_non_neg_args_cond(int dim);

        z3::expr loop_expression(Use* u);

        z3::expr as_loop_expression(Use* u);
        // z3::expr _as_loop_expression(Use* u, z3::expr acc);
        bool is_terminal(Value* v);

        std::set<PHINode*> get_header_defs(Value* v);

        bool is_bool(Value* v);

        rec_ty header_phi_as_rec(PHINode* phi);
        initial_ty header_phi_as_initial(PHINode* phi);
        rec_ty loop2rec(Loop* loop);
        initial_ty loop2initial(Loop* loop);
        z3::expr loop_bound(Loop* loop);
        
        z3::expr phi2ite_header(PHINode* phi);

        bool is_back_edge(BasicBlock* from, BasicBlock* to);

        void test_loop_condition();

        void get_loop_idx();

    private:
        std::unique_ptr<Module> m;
        Function* main;
        std::map<Function*, LoopInfo&> LIs;
        std::map<Function*, DominatorTree> DTs;
        std::map<Function*, PostDominatorTree> PDTs;
        bool verbose = false;
        z3::context z3ctx;
        PassBuilder PB;
        LoopAnalysisManager LAM;
        FunctionAnalysisManager FAM;
        CGSCCAnalysisManager CGAM;
        ModuleAnalysisManager MAM;
        std::map<BasicBlock*, z3::expr> path_conditions;
        std::map<BasicBlock*, std::set<Use*>> bb_conditions;
        std::set<Instruction*> visited_inst;
        std::set<Loop*> visited_loops;
        rec_solver rec_s;
        z3::expr_vector expression2solve;
        std::map<Loop*, int> loop2idx;
        std::map<Value*, z3::expr> array_info;
};

#endif