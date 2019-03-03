/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamCondition.h
 *
 * Defines a class for evaluating conditions in the Relational Algebra
 * Machine.
 *
 ***********************************************************************/

#pragma once

#include "BinaryConstraintOps.h"
#include "RamNode.h"
#include "RamRelation.h"
#include "RamValue.h"
#include "SymbolTable.h"

#include <algorithm>
#include <sstream>
#include <string>

#include <cstdlib>

namespace souffle {

/**
 * Abstract Class for RAM condition
 */
class RamCondition : public RamNode {
public:
    RamCondition(RamNodeType type) : RamNode(type) {}

    /** Create clone */
    RamCondition* clone() const override = 0;
};

/**
 * Conjunction
 */
class RamConjunction : public RamCondition {
protected:
    /** Left-hand side of conjunction */
    std::unique_ptr<RamCondition> lhs;

    /** Right-hand side of conjunction */
    std::unique_ptr<RamCondition> rhs;

public:
    RamConjunction(std::unique_ptr<RamCondition> l, std::unique_ptr<RamCondition> r)
            : RamCondition(RN_Conjunction), lhs(std::move(l)), rhs(std::move(r)) {}

    /** Get left-hand side of conjunction */
    const RamCondition& getLHS() const {
        assert(lhs);
        return *lhs;
    }

    /** Get right-hand side of conjunction */
    const RamCondition& getRHS() const {
        assert(rhs);
        return *rhs;
    }

    /** Print */
    void print(std::ostream& os) const override {
        os << "(";
        lhs->print(os);
        os << " and ";
        rhs->print(os);
        os << ")";
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        return {lhs.get(), rhs.get()};
    }

    /** Create clone */
    RamConjunction* clone() const override {
        RamConjunction* res = new RamConjunction(
                std::unique_ptr<RamCondition>(lhs->clone()), std::unique_ptr<RamCondition>(rhs->clone()));
        return res;
    }

    /** Apply */
    void apply(const RamNodeMapper& map) override {
        lhs = map(std::move(lhs));
        rhs = map(std::move(rhs));
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamConjunction*>(&node));
        const auto& other = static_cast<const RamConjunction&>(node);
        return getLHS() == other.getLHS() && getRHS() == other.getRHS();
    }
};

/**
 * Negation
 */
class RamNegation : public RamCondition {
protected:
    /** Operand */
    std::unique_ptr<RamCondition> operand;

public:
    RamNegation(std::unique_ptr<RamCondition> operand)
            : RamCondition(RN_Negation), operand(std::move(operand)) {}

    /** Get operand of negation */
    const RamCondition& getOperand() const {
        assert(nullptr != operand);
        return *operand;
    }

    /** Print */
    void print(std::ostream& os) const override {
        os << "(not ";
        operand->print(os);
        os << ")";
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        return {operand.get()};
    }

    /** Create clone */
    RamNegation* clone() const override {
        RamNegation* res = new RamNegation(std::unique_ptr<RamCondition>(operand->clone()));
        return res;
    }

    /** Apply */
    void apply(const RamNodeMapper& map) override {
        operand = map(std::move(operand));
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamNegation*>(&node));
        const auto& other = static_cast<const RamNegation&>(node);
        return getOperand() == other.getOperand();
    }
};

/**
 * Binary constraint
 */
class RamConstraint : public RamCondition {
private:
    /** Operator */
    BinaryConstraintOp op;

    /** Left-hand side of constraint*/
    std::unique_ptr<RamValue> lhs;

    /** Right-hand side of constraint */
    std::unique_ptr<RamValue> rhs;

public:
    RamConstraint(BinaryConstraintOp op, std::unique_ptr<RamValue> l, std::unique_ptr<RamValue> r)
            : RamCondition(RN_Constraint), op(op), lhs(std::move(l)), rhs(std::move(r)) {}

    /** Print */
    void print(std::ostream& os) const override {
        os << "(";
        lhs->print(os);
        os << " " << toBinaryConstraintSymbol(op) << " ";
        rhs->print(os);
        os << ")";
    }

    /** Get left-hand side */
    RamValue* getLHS() const {
        return lhs.get();
    }

    /** Get right-hand side */
    RamValue* getRHS() const {
        return rhs.get();
    }

    /** Get operator symbol */
    BinaryConstraintOp getOperator() const {
        return op;
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        return {lhs.get(), rhs.get()};
    }

    /** Create clone */
    RamConstraint* clone() const override {
        RamConstraint* res = new RamConstraint(
                op, std::unique_ptr<RamValue>(lhs->clone()), std::unique_ptr<RamValue>(rhs->clone()));
        return res;
    }

    /** Apply */
    void apply(const RamNodeMapper& map) override {
        lhs = map(std::move(lhs));
        rhs = map(std::move(rhs));
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamConstraint*>(&node));
        const auto& other = static_cast<const RamConstraint&>(node);
        return getOperator() == other.getOperator() && getLHS() == other.getLHS() &&
               getRHS() == other.getRHS();
    }
};

/**
 * Abstract existence check
 */
class RamAbstractExistenceCheck : public RamCondition {
protected:
    /* Relation */
    std::unique_ptr<RamRelationReference> relation;

    /** Pattern -- nullptr if undefined */
    std::vector<std::unique_ptr<RamValue>> values;

public:
    RamAbstractExistenceCheck(RamNodeType type, std::unique_ptr<RamRelationReference> rel,
            std::vector<std::unique_ptr<RamValue>> vals)
            : RamCondition(type), relation(std::move(rel)), values(std::move(vals)) {}

    /** Get relation */
    const RamRelationReference& getRelation() const {
        return *relation;
    }

    /** Get arguments */
    std::vector<RamValue*> getValues() const {
        return toPtrVector(values);
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res = {relation.get()};
        for (const auto& cur : values) {
            res.push_back(cur.get());
        }
        return res;
    }

    /** Apply */
    void apply(const RamNodeMapper& map) override {
        relation = map(std::move(relation));
        for (auto& val : values) {
            if (val != nullptr) {
                val = map(std::move(val));
            }
        }
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamAbstractExistenceCheck*>(&node));
        const auto& other = static_cast<const RamAbstractExistenceCheck&>(node);
        return getRelation() == other.getRelation() && equal_targets(values, other.values);
    }
};

/**
 * Existence check for a tuple(-pattern) in a relation
 */
class RamExistenceCheck : public RamAbstractExistenceCheck {
public:
    RamExistenceCheck(std::unique_ptr<RamRelationReference> rel, std::vector<std::unique_ptr<RamValue>> vals)
            : RamAbstractExistenceCheck(RN_ExistenceCheck, std::move(rel), std::move(vals)) {}

    /** Print */
    void print(std::ostream& os) const override {
        os << "("
           << join(values, ",",
                      [](std::ostream& out, const std::unique_ptr<RamValue>& value) {
                          if (!value) {
                              out << "_";
                          } else {
                              out << *value;
                          }
                      })
           << ") ∈ " << relation->getName();
    }

    /** Create clone */
    RamExistenceCheck* clone() const override {
        std::vector<std::unique_ptr<RamValue>> newValues;
        for (auto& cur : values) {
            RamValue* val = nullptr;
            if (cur != nullptr) {
                val = cur->clone();
            }
            newValues.emplace_back(val);
        }
        RamExistenceCheck* res = new RamExistenceCheck(
                std::unique_ptr<RamRelationReference>(relation->clone()), std::move(newValues));
        return res;
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamExistenceCheck*>(&node));
        return RamAbstractExistenceCheck::equal(node);
    }
};

/**
 * Existence check for a relation for provenance existence check
 */
class RamProvenanceExistenceCheck : public RamAbstractExistenceCheck {
public:
    RamProvenanceExistenceCheck(
            std::unique_ptr<RamRelationReference> rel, std::vector<std::unique_ptr<RamValue>> vals)
            : RamAbstractExistenceCheck(RN_ProvenanceExistenceCheck, std::move(rel), std::move(vals)) {}

    /** Print */
    void print(std::ostream& os) const override {
        os << "("
           << join(values, ",",
                      [](std::ostream& out, const std::unique_ptr<RamValue>& value) {
                          if (!value) {
                              out << "_";
                          } else {
                              out << *value;
                          }
                      })
           << ") prov∈ " << relation->getName();
    }

    /** Create clone */
    RamProvenanceExistenceCheck* clone() const override {
        std::vector<std::unique_ptr<RamValue>> newValues;
        for (auto& cur : values) {
            RamValue* val = nullptr;
            if (cur != nullptr) {
                val = cur->clone();
            }
            newValues.emplace_back(val);
        }
        RamProvenanceExistenceCheck* res = new RamProvenanceExistenceCheck(
                std::unique_ptr<RamRelationReference>(relation->clone()), std::move(newValues));
        return res;
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(dynamic_cast<const RamProvenanceExistenceCheck*>(&node));
        return RamAbstractExistenceCheck::equal(node);
    }
};

/**
 * Emptiness check for a relation
 */
class RamEmptinessCheck : public RamCondition {
    /** Relation */
    std::unique_ptr<RamRelationReference> relation;

public:
    RamEmptinessCheck(std::unique_ptr<RamRelationReference> rel)
            : RamCondition(RN_EmptinessCheck), relation(std::move(rel)) {}

    /** Get relation */
    const RamRelationReference& getRelation() const {
        return *relation;
    }

    /** Print */
    void print(std::ostream& os) const override {
        os << "(" << relation->getName() << " = ∅)";
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        return std::vector<const RamNode*>() = {relation.get()};
    }

    /** Create clone */
    RamEmptinessCheck* clone() const override {
        RamEmptinessCheck* res =
                new RamEmptinessCheck(std::unique_ptr<RamRelationReference>(relation->clone()));
        return res;
    }

    /** Apply */
    void apply(const RamNodeMapper& map) override {
        relation = map(std::move(relation));
    }

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamEmptinessCheck*>(&node));
        const auto& other = static_cast<const RamEmptinessCheck&>(node);
        return getRelation() == other.getRelation();
    }
};

}  // end of namespace souffle
