/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamOperationDepth.h
 *
 * Get the depth (number of nested operations) of a RAM operation
 *
 ***********************************************************************/

#pragma once

#include "RamAnalysis.h"

namespace souffle {

class RamOperation;
class RamTranslationUnit;

/*
 * Class to compute the depth
 */
class RamOperationDepthAnalysis : public RamAnalysis {
public:
    /** name of analysis */
    static constexpr const char* name = "operation-depth-analysis";

    /** run depth analysis for a RAM translation unit */
    void run(const RamTranslationUnit& translationUnit) override {}

    /** get depth */
    size_t getDepth(const RamOperation* op) const;
};

}  // end of namespace souffle
