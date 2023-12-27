#ifndef LOOP_TRANSFORMER_H
#define LOOP_TRANSFORMER_H
#include "llvm/IR/Function.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

class loop_transformer {
    public:
        loop_transformer(Function* main, LoopInfo& LI, Function* unknown_call): main(main), LI(LI), unknown_call(unknown_call), builder(main->getContext()) {}
        bool transform_function();
        bool transform_loop(Loop* loop);
        std::vector<BasicBlock*> get_region(Loop* loop, BasicBlock* bb);
        void transform_regions(std::vector<std::vector<BasicBlock*>>& regions);
        BasicBlock* get_exiting_for_region(std::vector<BasicBlock*>& region);
        bool is_loop_region(std::vector<BasicBlock*>& region);
    private:
        Function* main;
        LoopInfo& LI;
        Function* unknown_call;
        IRBuilder<> builder;
        BasicBlock* _transform_regions(std::vector<std::vector<BasicBlock*>>& regions, int start);
};

#endif