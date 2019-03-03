/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamConstValue.h
 *
 * Check whether a RAM value is constant
 *
 ***********************************************************************/

#pragma once

#include "RamAnalysis.h"

namespace souffle {

class RamValue;
class RamTranslationUnit;

/*
 * Class for a constant check
 */
class RamConstValueAnalysis : public RamAnalysis {
public:
    /** name of analysis */
    static constexpr const char* name = "const-value-analysis";

    /** run const value analysis for a RAM translation unit */
    void run(const RamTranslationUnit& translationUnit) override {}

    /** constant value */
    bool isConstant(const RamValue* v) const;
};

}  // end of namespace souffle
