#ifndef LOOP_TRANSFORMER_H
#define LOOP_TRANSFORMER_H
#include "llvm/IR/Function.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

typedef std::vector<BasicBlock*> region_ty;

class loop_transformer {
    public:
        loop_transformer(Function* main, LoopInfo& LI, Function* unknown_call): main(main), LI(LI), unknown_call(unknown_call), builder(main->getContext()) {}
        bool transform_function();
        bool transform_loop(Loop* loop);
        region_ty get_region(Loop* loop, BasicBlock* bb);
        std::pair<BasicBlock*, BasicBlock*> transform_regions(std::vector<region_ty>& regions);
        BasicBlock* get_exiting_for_region(region_ty& region);
        bool is_loop_region(region_ty& region);
        void print_region(region_ty& region);
        std::pair<BasicBlock*, BasicBlock*> transform_loop_region(region_ty& region);
    private:
        Function* main;
        LoopInfo& LI;
        Function* unknown_call;
        IRBuilder<> builder;
        std::pair<BasicBlock*, BasicBlock*> _transform_regions(std::vector<region_ty>& regions, int start);
};

#endif