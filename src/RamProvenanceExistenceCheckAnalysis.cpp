/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamProvenanceExistenceCheckAnalysis.cpp
 *
 * Implementation of RAM Provenance Existence Check Analysis
 *
 ***********************************************************************/

#include "RamProvenanceExistenceCheckAnalysis.h"
#include "RamOperation.h"
#include "RamTypes.h"

namespace souffle {

/** Get key */
SearchColumns RamProvenanceExistenceCheckAnalysis::getKey(
        const RamProvenanceExistenceCheck* provExistCheck) const {
    const auto values = provExistCheck->getValues();
    SearchColumns res = 0;
    // values.size() - 1 because we discard the height annotation
    for (std::size_t i = 0; i < values.size() - 1; i++) {
        if (values[i] != nullptr) {
            res |= (1 << i);
        }
    }
    return res;
}

/** Is key total */
bool RamProvenanceExistenceCheckAnalysis::isTotal(const RamProvenanceExistenceCheck* provExistCheck) const {
    for (const auto& cur : provExistCheck->getValues()) {
        if (cur == nullptr) {
            return false;
        }
    }
    return true;
}

}  // end of namespace souffle
