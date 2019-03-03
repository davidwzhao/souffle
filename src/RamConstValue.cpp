/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2019, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamConstValue.cpp
 *
 * Implementation of RAM Constant Value Analysis
 *
 ***********************************************************************/

#include "RamConstValue.h"
#include "RamValue.h"
#include "RamVisitor.h"
#include <vector>

namespace souffle {

/** Determine whether a RAM value is a constant */
bool RamConstValueAnalysis::isConstant(const RamValue* value) const {
    // visitor
    class ConstValueVisitor : public RamVisitor<bool> {
    public:
        // number
        bool visitNumber(const RamNumber& num) override {
            return true;
        }

        // tuple element access
        bool visitElementAccess(const RamElementAccess& elem) override {
            return false;
        }

        // auto increment
        bool visitAutoIncrement(const RamAutoIncrement& increment) override {
            return false;
        }

        // intrinsic functors
        bool visitIntrinsicOperator(const RamIntrinsicOperator& op) override {
            const auto& args = op.getArguments();
            bool isConst = true;
            for (const auto arg : args) {
                isConst = isConst && visit(arg);
            }
            return isConst;
        }

        // pack operator
        bool visitPack(const RamPack& pack) override {
            return false;
        }

        // argument
        bool visitArgument(const RamArgument& arg) override {
            return false;
        }

        // user defined operator
        bool visitUserDefinedOperator(const RamUserDefinedOperator& op) override {
            const auto& args = op.getArguments();
            bool isConst = true;
            for (const auto arg : args) {
                isConst = isConst && visit(arg);
            }
            return isConst;
        }
    };
    return ConstValueVisitor().visit(value);
}

}  // end of namespace souffle
