#include "loop_transformer.h"

bool loop_transformer::transform_function() {
    auto top_level_loops = LI.getTopLevelLoops();
    bool changed = false;
    for (Loop* loop : top_level_loops) {
        if (!loop->isInnermost()) {
            changed = transform_loop(loop);
        }
    }
    return changed;
}

bool loop_transformer::transform_loop(Loop* loop) {
    bool changed = false;
    BasicBlock* cur_bb = loop->getHeader();
    BasicBlock* header = loop->getHeader();
    int in_loop_idx = 0;
    for (auto bb : successors(cur_bb)) {
        if (loop->contains(bb)) {
            cur_bb = bb;
            break;
        }
        in_loop_idx++;
    }

    std::vector<region_ty> regions;
    while (loop->contains(cur_bb)) {
        region_ty cur_region = get_region(loop, cur_bb);
        regions.push_back(cur_region);
        BasicBlock* front = cur_region.front();
        if (LI.getLoopFor(front) == loop) {
            BasicBlock* exiting_bb = cur_region.back();
            cur_bb = exiting_bb->getSingleSuccessor();
            assert(cur_bb);
        } else {
            // errs() << "Loop region: " << cur_bb->getName() << "\n";
            Loop* sub_loop = LI.getLoopFor(cur_bb);
            cur_bb = sub_loop->getExitBlock();
            assert(cur_bb);
        }
        // }
        if (cur_bb == loop->getHeader()) break;
    }
    if (regions.size() >= 2) {
        auto new_header_latch = transform_regions(regions);
        auto header_br = dyn_cast_or_null<BranchInst>(header->getTerminator());
        header_br->setSuccessor(in_loop_idx, new_header_latch.first);
        builder.SetInsertPoint(new_header_latch.second);
        builder.CreateBr(header);
    }
    return changed;
}

std::pair<BasicBlock*, BasicBlock*>
loop_transformer::transform_regions(std::vector<region_ty>& regions) {
    auto& llvm_ctx = main->getContext();
    return _transform_regions(regions, 0);
}

bool loop_transformer::is_loop_region(region_ty& region) {
    return LI.isLoopHeader(region[0]);
}

BasicBlock* loop_transformer::get_exiting_for_region(region_ty& region) {
    if (is_loop_region(region)) {
        Loop* loop = LI.getLoopFor(region[0]);
        return loop->getExitingBlock();
    }
    return region.back();
}

std::pair<BasicBlock*, BasicBlock*>
loop_transformer::_transform_regions(std::vector<region_ty>& regions, int start) {
    auto& llvm_ctx = main->getContext();
    BasicBlock* guard = BasicBlock::Create(llvm_ctx, "loop.transform.guard", main);
    builder.SetInsertPoint(guard);
    auto call = builder.CreateCall(unknown_call);
    auto cmp = builder.CreateCmp(CmpInst::Predicate::ICMP_EQ, call, ConstantInt::getSigned(call->getType(), 0));
    BasicBlock* left_first_bb = regions[start].front();
    BasicBlock* right_first_bb = regions[start + 1].front();
    BasicBlock* exiting_left_bb = get_exiting_for_region(regions[start]);
    BasicBlock* exiting_right_bb = get_exiting_for_region(regions[start + 1]);
    if (is_loop_region(regions[start])) {
        auto left_entry_exiting = transform_loop_region(regions[start]);
        left_first_bb = left_entry_exiting.first;
        exiting_left_bb = left_entry_exiting.second;
    }
    if (regions.size() - start != 2) {
        auto right_guard_merge = _transform_regions(regions, start + 1);
        right_first_bb = right_guard_merge.first;
        exiting_right_bb = right_guard_merge.second;
    }
    builder.SetInsertPoint(guard);
    auto br = builder.CreateCondBr(cmp, left_first_bb, right_first_bb);
    if (exiting_left_bb->getTerminator())
        exiting_left_bb->getTerminator()->removeFromParent();
    if (exiting_right_bb->getTerminator())
        exiting_right_bb->getTerminator()->removeFromParent();
    BasicBlock* merge_bb = BasicBlock::Create(llvm_ctx, "loop.transform.merge", main);
    builder.SetInsertPoint(exiting_left_bb);
    builder.CreateBr(merge_bb);
    builder.SetInsertPoint(exiting_right_bb);
    builder.CreateBr(merge_bb);
    return {guard, merge_bb};
}

std::pair<BasicBlock*, BasicBlock*>
loop_transformer::transform_loop_region(region_ty& region) {
    assert(is_loop_region(region));
    BasicBlock* header = region.front();
    Loop* loop = LI.getLoopFor(header);
    assert(loop->isInnermost());
    BasicBlock* latch = loop->getLoopLatch();
    assert(latch);
    BasicBlock* exiting_bb = loop->getExitingBlock();
    assert(exiting_bb);
    BasicBlock* exit_bb = loop->getExitBlock();
    assert(exit_bb);
    Instruction* term = latch->getTerminator();
    BranchInst* latch_branch = dyn_cast_or_null<BranchInst>(term);
    assert(latch_branch);
    assert(latch_branch->isUnconditional());
    auto& llvm_ctx = main->getContext();
    BasicBlock* merge_bb = BasicBlock::Create(llvm_ctx, "loop.loop_transform.merge", main);
    Instruction* exiting_term = exiting_bb->getTerminator();
    BranchInst* exiting_branch = dyn_cast_or_null<BranchInst>(exiting_term);
    int exit_idx = exiting_branch->getSuccessor(0) == exit_bb ? 0 : 1;
    exiting_branch->setSuccessor(exit_idx, merge_bb);
    latch_branch->setSuccessor(0, merge_bb);
    return {header, merge_bb};
}

region_ty loop_transformer::get_region(Loop* loop, BasicBlock* bb) {
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

void loop_transformer::print_region(region_ty& region) {
    if (is_loop_region(region)) {
        errs() << "Loop Region: " << region[0]->getName() << "\n";
    } else {
        errs() << "Basic Region: ";
        for (auto bb : region) {
            errs() << bb->getName() << " ";
        }
        errs() << "\n";
    }
}