#include "structures.h"

using namespace llvm;

int find_bb(const BasicBlock* target, const path_ty& path) {
    int i = 0;
    for (i = 0; i < path.size(); i++) {
        if (target == path[i]) {
            break;
        }
    }
    return i;
}