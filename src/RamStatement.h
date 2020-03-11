/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file RamStatement.h
 *
 * Defines abstract class Statement and sub-classes for implementing the
 * Relational Algebra Machine (RAM), which is an abstract machine.
 *
 ***********************************************************************/

#pragma once

#include "RamExpression.h"
#include "RamNode.h"
#include "RamOperation.h"
#include "RamRelation.h"
#include "Util.h"

#include <algorithm>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

namespace souffle {

/**
 * @class RamStatement
 * @brief Abstract class for RAM statements
 */
class RamStatement : public RamNode {
public:
    /** @brief Pretty print with indentation */
    virtual void print(std::ostream& os, int tabpos) const = 0;

    void print(std::ostream& os) const override {
        print(os, 0);
    }

    RamStatement* clone() const override = 0;
};

/**
 * @class RamRelationStatement
 * @brief RAM Statements with a single relation
 */
class RamRelationStatement : public RamStatement {
public:
    RamRelationStatement(std::unique_ptr<RamRelationReference> relRef) : relationRef(std::move(relRef)) {
        assert(relationRef != nullptr && "Relation reference is a null-pointer");
    }

    /** @brief Get RAM relation */
    const RamRelation& getRelation() const {
        return *relationRef->get();
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {relationRef.get()};
    }

    void apply(const RamNodeMapper& map) override {
        relationRef = map(std::move(relationRef));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamRelationStatement&>(node);
        return getRelation() == other.getRelation();
    }

protected:
    /** Relation reference */
    std::unique_ptr<RamRelationReference> relationRef;
};

/**
 * @class RamIO
 * @brief I/O statement for a relation
 *
 * I/O operation for a relation, e.g., input/output/printsize
 */
class RamIO : public RamRelationStatement {
public:
    RamIO(std::unique_ptr<RamRelationReference> relRef, std::map<std::string, std::string> directives)
            : RamRelationStatement(std::move(relRef)), directives(std::move(directives)) {}

    /** @brief get I/O directives */
    const std::map<std::string, std::string>& getDirectives() const {
        return directives;
    }

    /** @get value of I/O directive */
    const std::string get(const std::string& key) const {
        return directives.at(key);
    }

    void print(std::ostream& os, int tabpos) const override {
        const RamRelation& rel = getRelation();
        os << times(" ", tabpos);
        os << "IO " << rel.getName() << " (";
        os << join(directives, ",", [](std::ostream& out, const auto& arg) {
            out << arg.first << "=\"" << escape(arg.second) << "\"";
        });
        os << ")" << std::endl;
    };

    RamIO* clone() const override {
        return new RamIO(std::unique_ptr<RamRelationReference>(relationRef->clone()), directives);
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamIO&>(node);
        return RamRelationStatement::equal(other) && directives == other.directives;
    }

protected:
    /** IO directives */
    std::map<std::string, std::string> directives;
};

/**
 * @class RamClear
 * @brief Delete tuples of a relation
 *
 * This retains the target relation, but cleans its content
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * CLEAR A
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamClear : public RamRelationStatement {
public:
    RamClear(std::unique_ptr<RamRelationReference> relRef) : RamRelationStatement(std::move(relRef)) {}

    void print(std::ostream& os, int tabpos) const override {
        const RamRelation& rel = getRelation();
        os << times(" ", tabpos);
        os << "CLEAR ";
        os << rel.getName();
        os << std::endl;
    }

    RamClear* clone() const override {
        return new RamClear(std::unique_ptr<RamRelationReference>(relationRef->clone()));
    }
};

/**
 * @class RamBinRelationStatement
 * @brief Abstract class for a binary relation
 *
 * Comprises two RamRelations
 */
class RamBinRelationStatement : public RamStatement {
public:
    RamBinRelationStatement(std::unique_ptr<RamRelationReference> f, std::unique_ptr<RamRelationReference> s)
            : first(std::move(f)), second(std::move(s)) {
        assert(first->get()->getArity() == second->get()->getArity() && "mismatching arities");

        assert(first != nullptr && "First relation is a null-pointer");
        assert(second != nullptr && "Second relation is a null-pointer");
        const auto& type1 = first->get()->getAttributeTypes();
        const auto& type2 = first->get()->getAttributeTypes();
        for (size_t i = 0; i < first->get()->getArity(); i++) {
            assert(type1[i] == type2[i] && "mismatching type");
        }
    }

    /** @brief Get first relation */
    const RamRelation& getFirstRelation() const {
        return *first->get();
    }

    /** @brief Get second relation */
    const RamRelation& getSecondRelation() const {
        return *second->get();
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {first.get(), second.get()};
    }

    void apply(const RamNodeMapper& map) override {
        first = map(std::move(first));
        second = map(std::move(second));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamBinRelationStatement&>(node);
        return getFirstRelation() == other.getFirstRelation() &&
               getSecondRelation() == other.getSecondRelation();
    }

protected:
    /** first argument of binary statement */
    std::unique_ptr<RamRelationReference> first;

    /** second argument of binary statement */
    std::unique_ptr<RamRelationReference> second;
};

/**
 * @class RamSemiMerge
 * @brief Merge tuples from a source into target relation, 
 * but only tuples that already existed in the target relation.
 * Used for updating counts, etc. for subsumption-related evaluation.
 *
 * Note that semantically uniqueness of tuples is not checked.
 *
 * The following example merges A into B:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * SEMIMERGE B WITH A
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamSemiMerge : public RamBinRelationStatement {
public:
    RamSemiMerge(std::unique_ptr<RamRelationReference> tRef, std::unique_ptr<RamRelationReference> sRef)
            : RamBinRelationStatement(std::move(sRef), std::move(tRef)) {}

    /** @brief Get source relation */
    const RamRelation& getSourceRelation() const {
        return getFirstRelation();
    }

    /** @brief Get target relation */
    const RamRelation& getTargetRelation() const {
        return getSecondRelation();
    }

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "SEMIMERGE " << getTargetRelation().getName() << " WITH " << getSourceRelation().getName();
        os << std::endl;
    }

    RamSemiMerge* clone() const override {
        auto* res = new RamSemiMerge(std::unique_ptr<RamRelationReference>(second->clone()),
                std::unique_ptr<RamRelationReference>(first->clone()));
        return res;
    }

protected:
    bool equal(const RamNode& node) const override {
        return RamBinRelationStatement::equal(node);
    }
};

/**
 * @class RamExtend
 * @brief Extend equivalence relation.
 *
 * The following example merges A into B:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * EXTEND B WITH A
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamExtend : public RamBinRelationStatement {
public:
    RamExtend(std::unique_ptr<RamRelationReference> tRef, std::unique_ptr<RamRelationReference> sRef)
            : RamBinRelationStatement(std::move(sRef), std::move(tRef)) {}

    /** @brief Get source relation */
    const RamRelation& getSourceRelation() const {
        return getFirstRelation();
    }

    /** @brief Get target relation */
    const RamRelation& getTargetRelation() const {
        return getSecondRelation();
    }

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "EXTEND " << getTargetRelation().getName() << " WITH " << getSourceRelation().getName();
        os << std::endl;
    }

    RamExtend* clone() const override {
        auto* res = new RamExtend(std::unique_ptr<RamRelationReference>(second->clone()),
                std::unique_ptr<RamRelationReference>(first->clone()));
        return res;
    }

protected:
    bool equal(const RamNode& node) const override {
        return RamBinRelationStatement::equal(node);
    }
};

/**
 * @class RamSwap
 * @brief Swap operation with respect to two relations
 *
 * Swaps the contents of the two relations
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * SWAP(A, B)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamSwap : public RamBinRelationStatement {
public:
    RamSwap(std::unique_ptr<RamRelationReference> f, std::unique_ptr<RamRelationReference> s)
            : RamBinRelationStatement(std::move(f), std::move(s)) {}

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos);
        os << "SWAP (" << getFirstRelation().getName() << ", " << getSecondRelation().getName() << ")";
        os << std::endl;
    };

    RamSwap* clone() const override {
        return new RamSwap(std::unique_ptr<RamRelationReference>(first->clone()),
                std::unique_ptr<RamRelationReference>(second->clone()));
    }

protected:
    bool equal(const RamNode& node) const override {
        return RamBinRelationStatement::equal(node);
    }
};

/**
 * @class RamQuery
 * @brief A relational algebra query
 *
 * Corresponds to the core machinery of semi-naive evaluation
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * QUERY
 *   FOR t0 in A
 *     FOR t1 in B
 *       ...
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamQuery : public RamStatement {
public:
    RamQuery(std::unique_ptr<RamOperation> o) : operation(std::move(o)) {
        assert(operation && "operation is a nullptr");
    }

    /** @brief Get RAM operation */
    const RamOperation& getOperation() const {
        return *operation;
    }

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "QUERY" << std::endl;
        operation->print(os, tabpos + 1);
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {operation.get()};
    }

    RamQuery* clone() const override {
        return new RamQuery(std::unique_ptr<RamOperation>(operation->clone()));
    }

    void apply(const RamNodeMapper& map) override {
        operation = map(std::move(operation));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamQuery&>(node);
        return getOperation() == other.getOperation();
    }

protected:
    /** RAM operation */
    std::unique_ptr<RamOperation> operation;
};

/**
 * @class RamListStatement
 * @brief Abstract class for a list of RAM statements
 */
class RamListStatement : public RamStatement {
public:
    RamListStatement() : RamStatement() {}

    /** @brief Get statements */
    std::vector<RamStatement*> getStatements() const {
        return toPtrVector(statements);
    }

    /** @brief Add new statement to the block */
    void add(std::unique_ptr<RamStatement> stmt) {
        if (stmt) {
            statements.push_back(std::move(stmt));
        }
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res;
        for (const auto& cur : statements) {
            res.push_back(cur.get());
        }
        return res;
    }

    void apply(const RamNodeMapper& map) override {
        for (auto& stmt : statements) {
            stmt = map(std::move(stmt));
        }
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamListStatement&>(node);
        return equal_targets(statements, other.statements);
    }

protected:
    /** ordered list of RAM statements */
    std::vector<std::unique_ptr<RamStatement>> statements;
};

/**
 * @class RamSequence
 * @brief Sequence of RAM statements
 *
 * Execute statement one by one from an ordered list of statements.
 */
class RamSequence : public RamListStatement {
public:
    RamSequence() : RamListStatement() {}

    template <typename... Stmts>
    RamSequence(std::unique_ptr<Stmts>&&... stmts) : RamListStatement() {
        // move all the given statements into the vector (not so simple)
        std::unique_ptr<RamStatement> tmp[] = {std::move(stmts)...};
        for (auto& cur : tmp) {
            statements.emplace_back(std::move(cur));
        }
        for (const auto& cur : statements) {
            (void)cur;
            assert(cur && "statement is a null-pointer");
        }
    }

    void print(std::ostream& os, int tabpos) const override {
        for (const auto& stmt : statements) {
            stmt->print(os, tabpos);
        }
    }

    RamSequence* clone() const override {
        auto* res = new RamSequence();
        for (auto& cur : statements) {
            res->statements.push_back(std::unique_ptr<RamStatement>(cur->clone()));
        }
        return res;
    }

protected:
    bool equal(const RamNode& node) const override {
        return RamListStatement::equal(node);
    }
};

/**
 * @class RamParallel
 * @brief Parallel block of statements
 *
 * Execute statements in parallel and wait until all statements have
 * completed their execution before completing the execution of the
 * parallel block.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * PARALLEL
 *   BEGIN DEBUG...
 *     QUERY
 *       ...
 * END PARALLEL
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamParallel : public RamListStatement {
public:
    RamParallel() : RamListStatement() {}

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "PARALLEL" << std::endl;
        for (auto const& stmt : statements) {
            stmt->print(os, tabpos + 1);
        }
        os << times(" ", tabpos) << "END PARALLEL" << std::endl;
    }

    RamParallel* clone() const override {
        auto* res = new RamParallel();
        for (auto& cur : statements) {
            res->add(std::unique_ptr<RamStatement>(cur->clone()));
        }
        return res;
    }

protected:
    bool equal(const RamNode& node) const override {
        return RamListStatement::equal(node);
    }
};

/**
 * @class RamLoop
 * @brief Execute statement until statement terminates loop via an exit statement
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * LOOP
 *   PARALLEL
 *     ...
 *   END PARALLEL
 * END LOOP
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamLoop : public RamStatement {
public:
    RamLoop(std::unique_ptr<RamStatement> b) : body(std::move(b)) {
        assert(body != nullptr && "Loop body is a null-pointer");
    }

    template <typename... Stmts>
    RamLoop(std::unique_ptr<RamStatement> f, std::unique_ptr<RamStatement> s, std::unique_ptr<Stmts>... rest)
            : body(std::make_unique<RamSequence>(std::move(f), std::move(s), std::move(rest)...)) {}

    /** @brief Get loop body */
    const RamStatement& getBody() const {
        return *body;
    }

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "LOOP" << std::endl;
        body->print(os, tabpos + 1);
        os << times(" ", tabpos) << "END LOOP" << std::endl;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {body.get()};
    }

    RamLoop* clone() const override {
        return new RamLoop(std::unique_ptr<RamStatement>(body->clone()));
    }

    void apply(const RamNodeMapper& map) override {
        body = map(std::move(body));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamLoop&>(node);
        return getBody() == other.getBody();
    }

protected:
    /** Body of loop */
    std::unique_ptr<RamStatement> body;
};

/**
 * @class RamExit
 * @brief Exit statement for a loop
 *
 * Exits a loop if exit condition holds.
 *
 * The following example will exit the loop given
 * that A is the empty set:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * EXIT (A = ∅)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamExit : public RamStatement {
public:
    RamExit(std::unique_ptr<RamCondition> c) : condition(std::move(c)) {
        assert(condition && "condition is a nullptr");
    }

    /** @brief Get exit condition */
    const RamCondition& getCondition() const {
        return *condition;
    }

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "EXIT " << getCondition() << std::endl;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return {condition.get()};
    }

    RamExit* clone() const override {
        return new RamExit(std::unique_ptr<RamCondition>(condition->clone()));
    }

    void apply(const RamNodeMapper& map) override {
        condition = map(std::move(condition));
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamExit&>(node);
        return getCondition() == other.getCondition();
    }

protected:
    /** exit condition */
    std::unique_ptr<RamCondition> condition;
};

/**
 * @class RamAbstractLog
 * @brief Abstract class for logging
 *
 * Comprises a RamStatement and the message (string) to be logged
 */
class RamAbstractLog {
public:
    RamAbstractLog(std::unique_ptr<RamStatement> stmt, std::string msg)
            : statement(std::move(stmt)), message(std::move(msg)) {
        assert(statement && "log statement is a nullptr");
    }

    std::vector<const RamNode*> getChildNodes() const {
        return {statement.get()};
    }

    /** @brief Get logging message */
    const std::string& getMessage() const {
        return message;
    }

    /** @brief Get logging statement */
    const RamStatement& getStatement() const {
        return *statement;
    }

    void apply(const RamNodeMapper& map) {
        statement = map(std::move(statement));
    }

protected:
    bool equal(const RamNode& node) const {
        const auto& other = dynamic_cast<const RamAbstractLog*>(&node);
        return getStatement() == other->getStatement() && getMessage() == other->getMessage();
    }

protected:
    /** logging statement */
    std::unique_ptr<RamStatement> statement;

    /** logging message */
    std::string message;
};

/**
 * @class RamLogRelationTimer
 * @brief Execution time logger for a statement
 *
 * Logs the execution time of a statement. Before and after
 * the execution of the logging statement the wall-clock time
 * is taken to compute the time duration for the statement.
 * Duration and logging message is printed after the execution
 * of the statement.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * START_TIMER ON A "file.dl [8:1-8:8]\;"
 *   ...
 * END_TIMER
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamLogRelationTimer : public RamRelationStatement, public RamAbstractLog {
public:
    RamLogRelationTimer(
            std::unique_ptr<RamStatement> stmt, std::string msg, std::unique_ptr<RamRelationReference> relRef)
            : RamRelationStatement(std::move(relRef)), RamAbstractLog(std::move(stmt), std::move(msg)) {}

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "START_TIMER ON " << getRelation().getName() << " \""
           << stringify(message) << "\"" << std::endl;
        statement->print(os, tabpos + 1);
        os << times(" ", tabpos) << "END_TIMER" << std::endl;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        std::vector<const RamNode*> res = RamRelationStatement::getChildNodes();
        res.push_back(RamAbstractLog::getChildNodes().at(0));
        return res;
    }

    RamLogRelationTimer* clone() const override {
        return new RamLogRelationTimer(std::unique_ptr<RamStatement>(statement->clone()), message,
                std::unique_ptr<RamRelationReference>(relationRef->clone()));
    }

    void apply(const RamNodeMapper& map) override {
        RamRelationStatement::apply(map);
        RamAbstractLog::apply(map);
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamLogRelationTimer&>(node);
        return RamRelationStatement::equal(other) && RamAbstractLog::equal(other);
    }
};

/**
 * @class RamLogTimer
 * @brief Execution time logger for a statement
 *
 * Logs the execution time of a statement. Before and after
 * the execution of the logging statement the wall-clock time
 * is taken to compute the time duration for the statement.
 * Duration and logging message is printed after the execution
 * of the statement.
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * START_TIMER "@runtime\;"
 *   BEGIN_STRATUM 0
 *     ...
 *   ...
 * END_TIMER
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamLogTimer : public RamStatement, public RamAbstractLog {
public:
    RamLogTimer(std::unique_ptr<RamStatement> stmt, std::string msg)
            : RamAbstractLog(std::move(stmt), std::move(msg)) {}

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "START_TIMER \"" << stringify(message) << "\"" << std::endl;
        statement->print(os, tabpos + 1);
        os << times(" ", tabpos) << "END_TIMER" << std::endl;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return RamAbstractLog::getChildNodes();
    }

    RamLogTimer* clone() const override {
        return new RamLogTimer(std::unique_ptr<RamStatement>(statement->clone()), message);
    }

    void apply(const RamNodeMapper& map) override {
        RamAbstractLog::apply(map);
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamLogTimer&>(node);
        return RamAbstractLog::equal(other);
    }
};

/**
 * @class RamDebugInfo
 * @brief Debug statement
 *
 * For example:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * BEGIN_DEBUG "gen(1) \nin file /file.dl [7:7-7:10]\;"
 *   ...
 * END_DEBUG
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
class RamDebugInfo : public RamStatement, public RamAbstractLog {
public:
    RamDebugInfo(std::unique_ptr<RamStatement> stmt, std::string msg)
            : RamAbstractLog(std::move(stmt), std::move(msg)) {}

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "BEGIN_DEBUG \"" << stringify(message) << "\"" << std::endl;
        statement->print(os, tabpos + 1);
        os << times(" ", tabpos) << "END_DEBUG" << std::endl;
    }

    std::vector<const RamNode*> getChildNodes() const override {
        return RamAbstractLog::getChildNodes();
    }

    RamDebugInfo* clone() const override {
        return new RamDebugInfo(std::unique_ptr<RamStatement>(statement->clone()), message);
    }

    void apply(const RamNodeMapper& map) override {
        RamAbstractLog::apply(map);
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamDebugInfo&>(node);
        return RamAbstractLog::equal(other);
    }
};

/**
 * @class RamLogSize
 * @brief Log relation size and a logging message.
 */
class RamLogSize : public RamRelationStatement {
public:
    RamLogSize(std::unique_ptr<RamRelationReference> relRef, std::string message)
            : RamRelationStatement(std::move(relRef)), message(std::move(message)) {}

    /** @brief Get logging message */
    const std::string& getMessage() const {
        return message;
    }

    void print(std::ostream& os, int tabpos) const override {
        os << times(" ", tabpos) << "LOGSIZE " << getRelation().getName();
        os << " TEXT "
           << "\"" << stringify(message) << "\"";
        os << std::endl;
    }

    RamLogSize* clone() const override {
        return new RamLogSize(std::unique_ptr<RamRelationReference>(relationRef->clone()), message);
    }

protected:
    bool equal(const RamNode& node) const override {
        const auto& other = static_cast<const RamLogSize&>(node);
        return RamRelationStatement::equal(other) && getMessage() == other.getMessage();
    }

protected:
    /** logging message */
    std::string message;
};

}  // end of namespace souffle
