/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamRelation.h
 *
 * Defines the class for ram relations
 ***********************************************************************/

#pragma once

#include "IODirectives.h"
#include "ParallelUtils.h"
#include "RamNode.h"
#include "RamTypes.h"
#include "RelationRepresentation.h"
#include "SymbolMask.h"
#include "SymbolTable.h"
#include "Table.h"
#include "Util.h"

#include <list>
#include <map>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * A RAM Relation in the RAM intermediate representation.
 */
class RamRelation : public RamNode {
protected:
    /** Name of relation */
    const std::string name;

    /** Arity, i.e., number of attributes */
    const size_t arity;

    /** Name of attributes */
    const std::vector<std::string> attributeNames;

    /** Type of attributes */
    const std::vector<std::string> attributeTypeQualifiers;

    /** TODO (#541): legacy, i.e., duplicated information */
    const SymbolMask mask;

    const RelationRepresentation representation;

public:
    RamRelation(const std::string name, const size_t arity, const std::vector<std::string> attributeNames,
            const std::vector<std::string> attributeTypeQualifiers, const SymbolMask mask,
            const RelationRepresentation representation)
            : RamNode(RN_Relation), name(std::move(name)), arity(arity),
              attributeNames(std::move(attributeNames)),
              attributeTypeQualifiers(std::move(attributeTypeQualifiers)), mask(std::move(mask)),
              representation(representation) {
        assert(this->attributeNames.size() == arity || this->attributeNames.empty());
        assert(this->attributeTypeQualifiers.size() == arity || this->attributeTypeQualifiers.empty());
    }

    /** Get name */
    const std::string& getName() const {
        return name;
    }

    /** Get argument */
    const std::string getArg(uint32_t i) const {
        if (!attributeNames.empty()) {
            return attributeNames[i];
        }
        if (arity == 0) {
            return "";
        }
        return "c" + std::to_string(i);
    }

    const std::string getArgTypeQualifier(uint32_t i) const {
        return (i < attributeTypeQualifiers.size()) ? attributeTypeQualifiers[i] : "";
    }

    /** Get symbol mask */
    const SymbolMask& getSymbolMask() const {
        return mask;
    }

    /** Is nullary relation */
    const bool isNullary() const {
        return arity == 0;
    }

    /** Relation representation type */
    const RelationRepresentation getRepresentation() const {
        return representation;
    }

    // Flag to check whether the data-structure
    const bool isCoverable() const {
        return true;
    }

    /** Is temporary relation (for semi-naive evaluation) */
    const bool isTemp() const {
        return name.at(0) == '@';
    }

    /* Get arity of relation */
    unsigned getArity() const {
        return arity;
    }

    /* Compare two relations via their name */
    bool operator<(const RamRelation& other) const {
        return name < other.name;
    }

    /* Print */
    void print(std::ostream& out) const override {
        out << name << "(";
        out << getArg(0);
        for (unsigned i = 1; i < arity; i++) {
            out << ",";
            out << getArg(i);
        }
        out << ")";

        out << " " << representation;
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        return std::vector<const RamNode*>();  // no child nodes
    }

    /** Create clone */
    RamRelation* clone() const override {
        RamRelation* res =
                new RamRelation(name, arity, attributeNames, attributeTypeQualifiers, mask, representation);
        return res;
    }

    /** Apply mapper */
    void apply(const RamNodeMapper& map) override {}

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamRelation*>(&node));
        const auto& other = static_cast<const RamRelation&>(node);
        return name == other.name && arity == other.arity && attributeNames == other.attributeNames &&
               attributeTypeQualifiers == other.attributeTypeQualifiers && mask == other.mask &&
               representation == other.representation && isTemp() == other.isTemp();
    }
};

/**
 * A RAM Relation in the RAM intermediate representation.
 */
class RamRelationReference : public RamNode {
protected:
    /** Name of relation */
    const RamRelation* relation;

public:
    RamRelationReference(const RamRelation* relation) : RamNode(RN_RelationReference), relation(relation) {}

    /** Get name */
    const std::string& getName() const {
        return relation->getName();
    }

    /** Get relation */
    const RamRelation* getRelation() const {
        return relation;
    }

    /** Get arity */
    unsigned getArity() const {
        return relation->getArity();
    }

    /** Is nullary relation */
    const bool isNullary() const {
        return relation->isNullary();
    }

    /** Relation representation type */
    const RelationRepresentation getRepresentation() const {
        return relation->getRepresentation();
    }

    /** Is temp relation */
    const bool isTemp() const {
        return relation->isTemp();
    }

    /** Get symbol mask */
    const SymbolMask& getSymbolMask() const {
        return relation->getSymbolMask();
    }

    /** Get argument */
    const std::string getArg(uint32_t i) const {
        return relation->getArg(i);
    }

    /** Get argument qualifier */
    const std::string getArgTypeQualifier(uint32_t i) const {
        return relation->getArgTypeQualifier(i);
    }

    /** Comparator */
    bool operator<(const RamRelationReference& other) const {
        return relation->operator<(*other.getRelation());
    }

    /* Print */
    void print(std::ostream& out) const override {
        out << getName();
    }

    /** Obtain list of child nodes */
    std::vector<const RamNode*> getChildNodes() const override {
        return std::vector<const RamNode*>();  // no child nodes
    }

    /** Create clone */
    RamRelationReference* clone() const override {
        auto* res = new RamRelationReference(relation);
        return res;
    }

    /** Apply mapper */
    void apply(const RamNodeMapper& map) override {}

protected:
    /** Check equality */
    bool equal(const RamNode& node) const override {
        assert(nullptr != dynamic_cast<const RamRelationReference*>(&node));
        const auto& other = static_cast<const RamRelationReference&>(node);
        return relation == other.relation;
    }
};

}  // end of namespace souffle
