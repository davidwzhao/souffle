/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamValueLevel.h
 *
 * Get level of value (which for-loop of a query)
 *
 ***********************************************************************/

#pragma once

#include "RamAnalysis.h"
#include "RamValue.h"

namespace souffle {

/*
 * Class for a level analysis
 */
class RamValueLevelAnalysis : public RamAnalysis {
public:
    /** name of analysis */
    static constexpr const char* name = "value-level-analysis";

    /** run level analysis for a RAM translation unit */
    void run(const RamTranslationUnit& translationUnit) override {}

    /** Get level */
    size_t getLevel(const RamValue* value) const;
};

}  // end of namespace souffle
