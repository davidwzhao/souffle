/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamExistenceCheckAnalysis.cpp
 *
 * Implementation of RAM Existence Check Analysis
 *
 ***********************************************************************/

#include "RamExistenceCheckAnalysis.h"
#include "RamOperation.h"
#include "RamTypes.h"

namespace souffle {

/** Get key */
SearchColumns RamExistenceCheckAnalysis::getKey(const RamExistenceCheck* existCheck) const {
    const auto values = existCheck->getValues();
    SearchColumns res = 0;
    for (std::size_t i = 0; i < values.size(); i++) {
        if (values[i] != nullptr) {
            res |= (1 << i);
        }
    }
    return res;
}

/** Is key total */
bool RamExistenceCheckAnalysis::isTotal(const RamExistenceCheck* existCheck) const {
    for (const auto& cur : existCheck->getValues()) {
        if (cur == nullptr) {
            return false;
        }
    }
    return true;
}

}  // end of namespace souffle
