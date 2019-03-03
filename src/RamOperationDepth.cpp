/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamOperationDepth.cpp
 *
 * Implementation of RAM Operation Depth Analysis
 *
 ***********************************************************************/

#include "RamOperationDepth.h"
#include "RamOperation.h"
#include "RamVisitor.h"

namespace souffle {

/** Get depth of query */
size_t RamOperationDepthAnalysis::getDepth(const RamOperation* op) const {
    // visitor
    class OperationDepthVisitor : public RamVisitor<size_t> {
    public:
        // nested operation
        size_t visitNestedOperation(const RamNestedOperation& nestedOp) override {
            return 1 + visit(nestedOp.getOperation());
        }

        // project
        size_t visitProject(const RamProject& project) override {
            return 1;
        }

        // return
        size_t visitReturn(const RamReturn& ret) override {
            return 1;
        }
    };
    return OperationDepthVisitor().visit(op);
}

}  // end of namespace souffle
