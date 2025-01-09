#ifndef STRUCTURE_H
#define STRUCTURE_H

#include "llvm/IR/BasicBlock.h"

using namespace llvm;

typedef std::vector<BasicBlock*> path_ty;

int find_bb(const BasicBlock* target, const path_ty& path);

#endif