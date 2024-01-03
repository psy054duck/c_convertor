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
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LCSSA.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/InstructionNamer.h"

#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Scalar/LoopFuse.h"
#include "llvm/Transforms/Scalar/LoopRotation.h"
#include "llvm/Transforms/Scalar/SROA.h"
#include "llvm/Transforms/Scalar/SCCP.h"
#include "llvm/Transforms/Scalar/IndVarSimplify.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/DCE.h"
#include "llvm/Transforms/Scalar/Reg2Mem.h"

#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Transforms/IPO/ModuleInliner.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "z3++.h"

#include <string>
#include <vector>
#include <map>
#include <set>
#include <fstream>

#include "rec_solver.h"
#include "smt_solver.h"
#include "loop_transformer.h"

using namespace llvm;
typedef std::vector<Use*> use_vector;
typedef std::vector<Value*> value_vector;
typedef std::pair<z3::expr, std::set<Value*>> pc_type;
typedef std::vector<BasicBlock*> path_ty;
typedef std::pair<Value*, std::vector<Use*>> array_access_ty;
typedef std::pair<BasicBlock*, BasicBlock*> edge_ty;

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
        validation_type check_assert_backward(Use* a, int out_idx);
        validation_type check_assert(Use* a, int out_idx);
        z3::expr_vector inst2z3(Instruction* inst, BasicBlock* prev_bb);
        z3::expr_vector all2z3(Instruction* inst);
        z3::expr use2z3(Use* u);
        z3::expr v2z3(Value* v, int dim = 0, int plus = 0);
        // z3::expr v2z3(Value* v);
        std::pair<Use*, bool> path_condition_b2b(BasicBlock* from, BasicBlock* to);
        std::set<Use*> get_bb_conditions(BasicBlock* bb);
        z3::expr path_condition_header2bb(BasicBlock* bb);
        z3::expr simple_path_condition_from_to(BasicBlock* from, BasicBlock* to);
        z3::expr path_condition_one_stride(BasicBlock* from, BasicBlock* To);
        z3::expr condition_from_path(path_ty& path);

        pc_type loop_condition(Loop* loop);

        int get_dim(Use* u);
        int get_dim(BasicBlock* bb);

        pc_type path_condition(BasicBlock* bb);
        pc_type path_condition_from_to(BasicBlock* from, BasicBlock* to);
        pc_type path_condition_from_to_straight(BasicBlock* from, BasicBlock* to);
        pc_type pc_and(const pc_type& a, const pc_type& b);
        pc_type pc_or(const pc_type& a, const pc_type& b);

        z3::expr express_v_as_header_phis(Value* v);
        z3::expr _express_v_as_header_phis(Value* v, Loop* target_loop);

        // z3::expr express_v_as_header_phis(Value* v, path_ty& path);
        z3::expr _express_v_as_header_phis(Value* v, path_ty& reversed_path);
        z3::expr path_condition_as_header_phis(path_ty& path);
        z3::expr _path_condition_as_header_phis(path_ty& path, int start);

        z3::func_decl get_z3_function(Value* v, int dim = 0);
        z3::func_decl get_z3_function(Use* u);

        z3::func_decl get_array_function(Value* v);
        z3::func_decl get_array_function(Value* v, int mem_id, int num_args);
        z3::func_decl get_array_function(Value* v, MemoryAccess* access);

        z3::expr_vector get_args(int dim, bool c = false, bool plus = false, bool prefix = false, Loop* loop=nullptr);
        z3::expr_vector get_args_0(int dim);
        z3::expr_vector get_args_N(Loop* loop);
        z3::expr_vector get_arr_args(int arity);
        z3::expr_vector get_pure_args(int dim, bool c);

        z3::expr_vector arr_access2z3(const std::vector<Use*>& args);
        z3::expr pairwise_eq(z3::expr_vector e1, z3::expr_vector e2);
        z3::expr get_non_neg_args_cond(int dim);

        z3::expr_vector path2z3(path_ty p);

        z3::expr loop_expression(Use* u);
        z3::expr get_z3_N(Loop* loop);

        z3::expr as_loop_expression(Use* u);
        // z3::expr _as_loop_expression(Use* u, z3::expr acc);
        bool is_terminal(Value* v);

        z3::sort_vector get_sorts(int num);

        bool encounter_mem_phi(Value* v);

        std::set<PHINode*> get_header_defs(Value* v);

        bool is_bool(Value* v);
        bool is_header_phi(Value* v, Loop* loop);

        rec_ty header_phi_as_rec(PHINode* phi);
        rec_ty header_phi_as_rec_nested(PHINode* phi);
        initial_ty header_phi_as_initial(PHINode* phi);
        rec_ty loop2rec(Loop* loop);
        initial_ty loop2initial(Loop* loop);
        z3::expr loop_bound(Loop* loop, rec_solver& rec_s);
        std::pair<closed_form_ty, rec_solver> solve_loop(Loop* loop);
        
        z3::expr phi2ite_header(PHINode* phi);
        std::pair<z3::expr, z3::expr> _phi2ite_header(PHINode* phi, BasicBlock* merge_bb);
        z3::expr phi2ite_find_path_condition(BasicBlock* from, BasicBlock* to);
        z3::expr phi2ite_find_path_condition_one_step(BasicBlock* from, BasicBlock* to);

        bool is_back_edge(BasicBlock* from, BasicBlock* to);
        bool is_back_edge_loop(Loop* loop, BasicBlock* from, BasicBlock* to);

        void test_loop_condition();

        void get_loop_idx();

        std::vector<path_ty> get_paths_from_to(BasicBlock* from, BasicBlock* to);
        std::vector<path_ty> get_paths_from_to_loop(Loop* loop);
        std::vector<path_ty> _get_paths_from_to_loop(Loop* loop, BasicBlock* cur_bb, std::vector<edge_ty> visited_edges);

        void print_path(path_ty);
        // Value* get_array_from_load_store(Value* v);
        array_access_ty get_array_access_from_load_store(Value* v);
        array_access_ty get_array_access_from_gep(GetElementPtrInst* gep);
        z3::expr_vector get_access_index(Value* v);

        z3::expr assertion2z3(Use* a);
        z3::expr_vector bb2z3(BasicBlock* bb, BasicBlock* prev_bb);
        z3::expr_vector loop2z3(Loop* loop, BasicBlock* prev_bb);

        int get_arity(Value* v);

        z3::expr_vector mem_header_phi2z3(Value* v);
        z3::expr_vector initial_mem_phi2z3(MemoryAccess* access, MemoryPhi* phi);
        z3::expr_vector latch_mem_phi2z3(MemoryAccess* access, MemoryPhi* phi);


        MemoryAccess* get_mem_use(Value* v);
        std::string get_array_name(Value* v, int mem_id);

        int get_m_phi_def_id(MemoryAccess* access);
        BasicBlock* get_bb_from_m_access(MemoryAccess* access);

        z3::expr_vector simplify_using_closed(z3::expr_vector vec);
        z3::expr_vector simplify_using_closed(z3::expr e);

        Loop* get_loop(BasicBlock* bb);

        rec_ty m_header_phi_as_rec(MemoryAccess* m_phi);
        z3::expr m_as_header_phi(Value* v, MemoryAccess* access, Loop* loop);
        bool is_m_header_phi(MemoryAccess* access, Loop* loop);

        void analyze_module_pre(ModulePassManager& MPM);
        void analyze_module_post(ModulePassManager& MPM);

        std::vector<PHINode*> get_all_phi_nodes(Function* f);
        int get_successor_index(BranchInst* br, const BasicBlock* bb);
        void clear_all_info();
        Value* find_def_chain_in_block(Value* v, BasicBlock* bb);
    private:
        std::unique_ptr<Module> m;
        Function* main;
        Function* unknown_fn;
        std::map<Function*, LoopInfo&> LIs;
        std::map<Function*, DominatorTree> DTs;
        std::map<Function*, PostDominatorTree> PDTs;
        std::map<Function*, MemorySSA&> MSSAs;
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
        std::map<Value*, z3::expr_vector> array_info;
        std::vector<closed_form_ty> cached_closed;
        std::map<Value*, int> array_index;
        std::map<Value*, z3::func_decl> array_z3_func;
        std::map<Value*, BasicBlock*> array_def_block;
        Value* _find_def_chain_in_block(Value* v, BasicBlock* bb, std::set<Value*>& visited_v);
        BasicBlock* find_nearest_common_dominator_phi(DominatorTree& DT, PHINode* phi);
};

#endif