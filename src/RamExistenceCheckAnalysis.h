/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamExistenceCheckAnalysis.h
 *
 * Get the index pattern of a RAM existence check
 *
 ***********************************************************************/

#pragma once

#include "RamAnalysis.h"
#include "RamTypes.h"

namespace souffle {

class RamExistenceCheck;

/*
 * Class to compute the index pattern
 */
class RamExistenceCheckAnalysis : public RamAnalysis {
public:
    /** name of analysis */
    static constexpr const char* name = "existence-check-analysis";

    /** run existence check analysis for a RAM translation unit */
    void run(const RamTranslationUnit& translationUnit) override {}

    /** get key */
    SearchColumns getKey(const RamExistenceCheck* existCheck) const;

    /** is key total */
    bool isTotal(const RamExistenceCheck* existCheck) const;
};

}  // end of namespace souffle
