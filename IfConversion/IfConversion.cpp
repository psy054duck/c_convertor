#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/LoopInfo.h"

#include "IfConversion.h"

using namespace llvm;

// struct IfConversion: PassInfoMixin<IfConversion> {
//   // Main entry point, takes IR unit to run the pass on (&F) and the
//   // corresponding pass manager (to be queried if need be)
//   PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
// 
//     return PreservedAnalyses::none();
//   }
// 
//   // Without isRequired returning true, this pass will be skipped for functions
//   // decorated with the optnone LLVM attribute. Note that clang -O0 decorates
//   // all functions with optnone.
//   static bool isRequired() { return true; }
// };
PreservedAnalyses IfConversionPass::run(Function &F, FunctionAnalysisManager& FAM) {
    IRBuilder<> builder(F.getContext());
    DominatorTree DT(F);
    PostDominatorTree PDT(F);
    LoopInfo LI(DT);

    for (auto &bb : F) {
        bool has_back_edge = false;
        std::vector<PHINode*> phis;
        for (auto &p : bb.phis()) {
            phis.push_back(&p);
        }
        if (phis.empty()) continue;
        const Loop* loop = LI.getLoopFor(&bb);
        int depth = LI.getLoopDepth(&bb);
        if (loop) {
            for (auto pred = pred_begin(&bb); pred != pred_end(&bb); pred++) {
                (*pred)->printAsOperand(errs(), false);
                if (loop->contains(*pred) && depth == LI.getLoopDepth(*pred) && loop->isLoopLatch(*pred)) {
                    has_back_edge = true;
                    break;
                }
            }
        }

        if (has_back_edge) continue;

        for (PHINode* phi : phis) {
            if (phi->getNumIncomingValues() == 2) {
                BasicBlock* curB = phi->getParent();
                BasicBlock* bb0 = phi->getIncomingBlock(0);
                BasicBlock* bb1 = phi->getIncomingBlock(1);
                BasicBlock* domB = DT.findNearestCommonDominator(bb0, bb1);
                if (!PDT.dominates(curB, domB)) continue;
                Instruction* term = domB->getTerminator();
                BranchInst* branch = dyn_cast<BranchInst>(term);
                if (!branch || !branch->isConditional()) continue;
                Value* condV = branch->getCondition();
                BasicBlock* true_b = bb0;
                BasicBlock* false_b = bb1;
                if (DT.dominates(branch->getSuccessor(0), bb0) || DT.dominates(branch->getSuccessor(1), bb1)) {
                    true_b = bb0;
                    false_b = bb1;
                } else {
                    true_b = bb1;
                    false_b = bb0;
                }
                int true_idx = phi->getBasicBlockIndex(true_b);
                int false_idx = phi->getBasicBlockIndex(false_b);
                Value* new_select = builder.CreateSelect(condV, phi->getIncomingValue(true_idx), phi->getIncomingValue(false_idx));
                ReplaceInstWithInst(phi, dyn_cast<Instruction>(new_select));
                // phi->replaceAllUsesWith(new_select);
                // new_select->takeName(phi);
                // phi->eraseFromParent();
                // errs() << *dyn_cast<Instruction>(new_select) << "\n";
            }
        }
    }
    return PreservedAnalyses::none();
}

llvm::PassPluginLibraryInfo getIfConversionPluginInfo() {
    return {LLVM_PLUGIN_API_VERSION, "IfConversion", LLVM_VERSION_STRING,
            [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, FunctionPassManager &FPM,
                    ArrayRef<PassBuilder::PipelineElement>) {
                    if (Name == "if-conversion") {
                        FPM.addPass(IfConversionPass());
                            return true;
                        }
                        return false;
                    });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getIfConversionPluginInfo();
}
