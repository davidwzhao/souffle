/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamConditionLevel.cpp
 *
 * Implementation of RAM Condition Level Analysis
 *
 ***********************************************************************/

#include "RamConditionLevel.h"
#include "RamCondition.h"
#include "RamTranslationUnit.h"
#include "RamValueLevel.h"
#include "RamVisitor.h"
#include <algorithm>
#include <vector>

namespace souffle {

/** run level analysis for a RAM translation unit */
void RamConditionLevelAnalysis::run(const RamTranslationUnit& translationUnit) {
    rvla = translationUnit.getAnalysis<RamValueLevelAnalysis>();
}

/** Get level of condition (which for-loop of a query) */
size_t RamConditionLevelAnalysis::getLevel(const RamCondition* condition) const {
    // visitor
    class ConditionLevelVisitor : public RamVisitor<size_t> {
        RamValueLevelAnalysis* rvla;

    public:
        ConditionLevelVisitor(RamValueLevelAnalysis* rvla) : rvla(rvla) {}

        // conjunction
        size_t visitConjunction(const RamConjunction& conj) override {
            return std::max(visit(conj.getLHS()), visit(conj.getRHS()));
        }

        // negation
        size_t visitNegation(const RamNegation& neg) override {
            return visit(neg.getOperand());
        }

        // constraint
        size_t visitConstraint(const RamConstraint& binRel) override {
            return std::max(rvla->getLevel(binRel.getLHS()), rvla->getLevel(binRel.getRHS()));
        }

        // existence check
        size_t visitExistenceCheck(const RamExistenceCheck& exists) override {
            size_t level = 0;
            for (const auto& cur : exists.getValues()) {
                if (cur) {
                    level = std::max(level, rvla->getLevel(cur));
                }
            }
            return level;
        }

        // provenance existence check
        size_t visitProvenanceExistenceCheck(const RamProvenanceExistenceCheck& provExists) override {
            size_t level = 0;
            for (const auto& cur : provExists.getValues()) {
                if (cur) {
                    level = std::max(level, rvla->getLevel(cur));
                }
            }
            return level;
        }

        // emptiness check
        size_t visitEmptinessCheck(const RamEmptinessCheck& emptiness) override {
            return 0;  // can be in the top level
        }
    };
    return ConditionLevelVisitor(rvla).visit(condition);
}

}  // end of namespace souffle
