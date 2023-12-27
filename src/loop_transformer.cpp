#include "loop_transformer.h"

bool loop_transformer::transform_function() {
    auto top_level_loops = LI.getTopLevelLoops();
    bool changed = false;
    for (Loop* loop : top_level_loops) {
        if (transform_loop(loop)) changed = true;
    }
    return changed;
}

bool loop_transformer::transform_loop(Loop* loop) {
    bool changed = false;
    BasicBlock* cur_bb = loop->getHeader();
    for (auto bb : successors(cur_bb)) {
        if (loop->contains(bb)) {
            cur_bb = bb;
            break;
        }
    }
    std::vector<std::vector<BasicBlock*>> regions;
    while (loop->contains(cur_bb)) {
        // if (LI.getLoopFor(cur_bb) != loop) {
        //     assert(LI.isLoopHeader(cur_bb));
        //     errs() << "Loop region: " << cur_bb->getName() << "\n";
        //     Loop* sub_loop = LI.getLoopFor(cur_bb);
        //     cur_bb = sub_loop->getExitBlock();
        //     assert(cur_bb);
        // } else {
        std::vector<BasicBlock*> cur_region = get_region(loop, cur_bb);
        regions.push_back(cur_region);
        BasicBlock* front = cur_region.front();
        if (LI.getLoopFor(front) == loop) {
            errs() << "basic region: ";
            for (auto bb : cur_region) {
                errs() << bb->getName() << " ";
            }
            errs() << "\n";
            BasicBlock* exiting_bb = cur_region.back();
            cur_bb = exiting_bb->getSingleSuccessor();
            assert(cur_bb);
        } else {
            errs() << "Loop region: " << cur_bb->getName() << "\n";
            Loop* sub_loop = LI.getLoopFor(cur_bb);
            cur_bb = sub_loop->getExitBlock();
            assert(cur_bb);
        }
        // }
        if (cur_bb == loop->getHeader()) break;
    }
    return changed;
}

void loop_transformer::transform_regions(std::vector<std::vector<BasicBlock*>>& regions) {
    auto& llvm_ctx = main->getContext();
    if (regions.size() == 1) {
        return;
    }
    if (regions.size() == 2) {
        BasicBlock* guard = BasicBlock::Create(llvm_ctx);
    }
    for (int i = 0; i < (int) regions.size() - 1; i++) {
        BasicBlock* guard = BasicBlock::Create(llvm_ctx);
        builder.SetInsertPoint(guard);
        auto call = builder.CreateCall(unknown_call);
        auto br = builder.CreateCondBr(call, regions[0][0], regions[1][0]);
    }
}

bool loop_transformer::is_loop_region(std::vector<BasicBlock*>& region) {
    return LI.isLoopHeader(region[0]);
}

BasicBlock* loop_transformer::get_exiting_for_region(std::vector<BasicBlock*>& region) {
    if (is_loop_region(region)) {
        Loop* loop = LI.getLoopFor(region[0]);
        return loop->getExitingBlock();
    }
    return region.back();
}

BasicBlock* loop_transformer::_transform_regions(std::vector<std::vector<BasicBlock*>>& regions, int start) {
    auto& llvm_ctx = main->getContext();
    BasicBlock* guard = BasicBlock::Create(llvm_ctx);
    auto call = builder.CreateCall(unknown_call);
    BasicBlock* merge_bb = BasicBlock::Create(llvm_ctx);
    if (regions.size() - start == 2) {
        auto br = builder.CreateCondBr(call, regions[start][0], regions[start + 1][0]);
        BasicBlock* exiting_left_bb = get_exiting_for_region(regions[start]);
        BasicBlock* exiting_right_bb = get_exiting_for_region(regions[start + 1]);
        exiting_left_bb->getTerminator()->removeFromParent();
        exiting_right_bb->getTerminator()->removeFromParent();
        builder.SetInsertPoint(exiting_left_bb);
        builder.CreateBr(merge_bb);
        builder.SetInsertPoint(exiting_right_bb);
        builder.CreateBr(merge_bb);
    } else {
        
    }
    return guard;
}

std::vector<BasicBlock*> loop_transformer::get_region(Loop* loop, BasicBlock* bb) {
    Loop* bb_loop = LI.getLoopFor(bb);
    std::vector<BasicBlock*> res{bb};
    if (bb_loop != loop) return res;
    // Instruction* bb_terminator = bb->getTerminator();
    // auto terminator_br = dyn_cast_or_null<BranchInst>(bb_terminator);
    // assert(terminator_br);
    // assert(terminator_br->isUnconditional());
    BasicBlock* cur_bb = bb->getSingleSuccessor();
    if (bb_loop->isLoopExiting(bb)) {
        for (auto succ : successors(bb)) {
            if (bb_loop->contains(succ)) {
                cur_bb = succ;
                break;
            }
        }
    }
    while (cur_bb && LI.getLoopFor(cur_bb) == bb_loop && bb_loop->getHeader() != cur_bb) {
        res.push_back(cur_bb);
        cur_bb = cur_bb->getSingleSuccessor();
    }
    return res;
}