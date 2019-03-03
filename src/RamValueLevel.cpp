/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamValueLevel.cpp
 *
 * Implementation of RAM Value Level Analysis
 *
 ***********************************************************************/

#include "RamValueLevel.h"
#include "RamVisitor.h"
#include <algorithm>

namespace souffle {

/** Get level of value (which for-loop of a query) */
size_t RamValueLevelAnalysis::getLevel(const RamValue* value) const {
    // visitor
    class ValueLevelVisitor : public RamVisitor<size_t> {
    public:
        // number
        size_t visitNumber(const RamNumber& num) override {
            return 0;
        }

        // tuple element access
        size_t visitElementAccess(const RamElementAccess& elem) override {
            return elem.getLevel();
        }

        // auto increment
        size_t visitAutoIncrement(const RamAutoIncrement& increment) override {
            return 0;
        }

        // intrinsic functors
        size_t visitIntrinsicOperator(const RamIntrinsicOperator& op) override {
            size_t level = 0;
            for (const auto& arg : op.getArguments()) {
                if (arg != nullptr) {
                    level = std::max(level, visit(arg));
                }
            }
            return level;
        }

        // pack operator
        size_t visitPack(const RamPack& pack) override {
            size_t level = 0;
            for (const auto& arg : pack.getArguments()) {
                if (arg) {
                    level = std::max(level, visit(arg));
                }
            }
            return level;
        }

        // argument
        size_t visitArgument(const RamArgument& arg) override {
            return 0;
        }

        // user defined operator
        size_t visitUserDefinedOperator(const RamUserDefinedOperator& op) override {
            size_t level = 0;
            for (const auto& arg : op.getArguments()) {
                if (arg != nullptr) {
                    level = std::max(level, visit(arg));
                }
            }
            return level;
        }
    };
    return ValueLevelVisitor().visit(value);
}

}  // end of namespace souffle
