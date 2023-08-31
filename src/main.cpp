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
#include "c2z3.h"

using namespace llvm;

int main(int argc, char** argv) {

    LLVMContext ctx;
    SMDiagnostic Err;
    std::unique_ptr<Module> mod(parseIRFile(argv[1], Err, ctx));

    c2z3 c_convertor(mod);
    use_vector assertions = c_convertor.getAllAssertions();
    // c_convertor.test_loop_condition();
    int i = 0;
    for (auto a : assertions) {
        Instruction* inst = dyn_cast<Instruction>(a->getUser());
        BasicBlock* bb = inst->getParent();
        // errs() << bb->getName() << "\n";
        // pc_type pc = c_convertor.path_condition(bb);
        // errs() << pc.first.to_string() << "\n";
        // errs() << c_convertor.path_condition(bb).to_string() << "\n";

        validation_type check_res = c_convertor.check_assert(a, i);
        errs() << get_validation_type_name(check_res) << "\n";
        i++;
        // errs() << c_convertor.use2z3(a).to_string() << "\n";
    }

}
