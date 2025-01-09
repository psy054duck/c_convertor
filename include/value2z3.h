#ifndef VALUE2Z3_H
#define VALUE2Z3_H

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
#include "structures.h"

using namespace llvm;

typedef std::vector<BasicBlock*> path_ty;
class value2z3 {
    public:
        value2z3(Function* F, z3::context& _z3ctx);
        z3::expr v2z3(Value* v, int dim = 0, int plus = false);
        z3::expr_vector inst2z3(Instruction* inst, BasicBlock* prev_bb);
        z3::expr express_v_as_inputs(Value* v, int dim, path_ty& path);
        z3::expr get_z3_formal_application(Function* f);
        z3::expr_vector get_z3_formal_parameters(Function* f);
        z3::func_decl get_z3_function(Function* f, int arity=-1);

        z3::context& get_context() { return z3ctx; }
    private:
        z3::context& z3ctx;
        Function* F;
        std::map<Loop*, int> loop2idx;
        FunctionAnalysisManager FAM;
        LoopAnalysisManager LA;
        z3::expr_vector get_args(int dim, bool c = false, bool plus = false, bool prefix = false, Loop* loop = nullptr);
        z3::func_decl get_z3_function(Value* v, int dim = 0);
        z3::func_decl get_z3_function(Use* u);
        z3::expr use2z3(Use* u);
        bool is_header_phi(Value* v, Loop* loop);
        bool is_bool(Value* v);
        void get_loop_idx();
        z3::sort_vector get_sorts(int num);
        bool is_parameter(Value* v);
};

#endif