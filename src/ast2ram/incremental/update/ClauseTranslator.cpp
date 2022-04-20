/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ClauseTranslator.cpp
 *
 ***********************************************************************/

#include "ast2ram/incremental/update/ClauseTranslator.h"
#include "Global.h"
#include "ast/Argument.h"
#include "ast/Atom.h"
#include "ast/Clause.h"
#include "ast/Variable.h"
#include "ast/utility/Utils.h"
#include "ast2ram/utility/Location.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ast2ram/utility/ValueIndex.h"
#include "ast2ram/incremental/Utils.h"
#include "ast2ram/seminaive/ClauseTranslator.h"
#include "ram/Aggregate.h"
#include "ram/Constraint.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Expression.h"
#include "ram/Filter.h"
#include "ram/GuardedInsert.h"
#include "ram/IfNotExists.h"
#include "ram/IntrinsicOperator.h"
#include "ram/IterationNumber.h"
#include "ram/Negation.h"
#include "ram/Operation.h"
#include "ram/ProvenanceExistenceCheck.h"
#include "ram/Scan.h"
#include "ram/Sequence.h"
#include "ram/SignedConstant.h"
#include "ram/Statement.h"
#include "ram/TupleElement.h"
#include "ram/UndefValue.h"
#include "souffle/utility/StringUtil.h"

namespace souffle::ast2ram::incremental::update {

/*
void ClauseTranslator::setDiffVersion(std::size_t diffVersion) {
    this->diffVersion = diffVersion;
}
*/

Own<ram::Statement> ClauseTranslator::translateNonRecursiveClause(const ast::Clause& clause) {

    VecOwn<ram::Statement> result;

    for (std::size_t diffVersion = 0; diffVersion < ast::getBodyLiterals<ast::Atom>(clause).size(); diffVersion++) {
        // Update diffVersion config
        this->diffVersion = diffVersion;

        appendStmt(result, seminaive::ClauseTranslator::translateNonRecursiveClause(clause));
    }

    this->diffVersion = 0;

    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Statement> ClauseTranslator::translateRecursiveClause(
        const ast::Clause& clause, const std::set<const ast::Relation*>& scc, std::size_t version) {

    VecOwn<ram::Statement> result;

    const auto& bodyLiterals = ast::getBodyLiterals<ast::Atom>(clause);

    for (std::size_t diffVersion = 0; diffVersion < bodyLiterals.size(); diffVersion++) {
        // Update diffVersion config
        this->diffVersion = diffVersion;

        if (mode == IncrementalUpdatedDiffMinus || mode == IncrementalUpdatedDiffPlus) {
            // Only translated updated diff_minus/diff_plus for recursive body atoms
            if (contains(scc, context.getProgram()->getRelation(*bodyLiterals[diffVersion]))) {
                std::cout << "making updated rule version for " << *(bodyLiterals[diffVersion]) << std::endl;
                appendStmt(result, seminaive::ClauseTranslator::translateRecursiveClause(clause, scc, version));
            }
        } else {
            appendStmt(result, seminaive::ClauseTranslator::translateRecursiveClause(clause, scc, version));
        }
    }

    this->diffVersion = 0;

    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Operation> ClauseTranslator::addNegatedDeltaAtom(
        Own<ram::Operation> op, const ast::Atom* atom) const {
    std::size_t arity = atom->getArity();
    std::string name = getDeltaRelationName(atom->getQualifiedName());

    if (arity == 0) {
        // for a nullary, negation is a simple emptiness check
        return mk<ram::Filter>(mk<ram::EmptinessCheck>(name), std::move(op));
    }

    // else, we construct the atom and create a negation
    VecOwn<ram::Expression> values;
    auto args = atom->getArguments();
    for (const auto* arg : args) {
        values.push_back(context.translateValue(*valueIndex, arg));
    }
    values.push_back(mk<ram::UndefValue>());
    values.push_back(mk<ram::UndefValue>());

    return mk<ram::Filter>(
            mk<ram::Negation>(mk<ram::ExistenceCheck>(name, std::move(values))), std::move(op));

    // For incremental evaluation, the delta check is enforced during merge time so does not need to be checked during rule evaluation
    // return nullptr;
}

std::string ClauseTranslator::getClauseAtomName(const ast::Clause& clause, const ast::Atom* atom) const {
    /* TODO: incremental does not currently work with subsumptive clauses
    if (isA<ast::SubsumptiveClause>(clause)) {
        // find the dominated / dominating heads
        const auto& body = clause.getBodyLiterals();
        auto dominatedHeadAtom = dynamic_cast<const ast::Atom*>(body[0]);
        auto dominatingHeadAtom = dynamic_cast<const ast::Atom*>(body[1]);

        if (clause.getHead() == atom) {
            if (mode == SubsumeDeleteCurrentDelta || mode == SubsumeDeleteCurrentCurrent) {
                return getDeleteRelationName(atom->getQualifiedName());
            }
            return getRejectRelationName(atom->getQualifiedName());
        }

        if (dominatedHeadAtom == atom) {
            if (mode == SubsumeDeleteCurrentDelta || mode == SubsumeDeleteCurrentCurrent) {
                return getConcreteRelationName(atom->getQualifiedName());
            }
            return getNewRelationName(atom->getQualifiedName());
        }

        if (dominatingHeadAtom == atom) {
            switch (mode) {
                case SubsumeRejectNewCurrent:
                case SubsumeDeleteCurrentCurrent: return getConcreteRelationName(atom->getQualifiedName());
                case SubsumeDeleteCurrentDelta: return getDeltaRelationName(atom->getQualifiedName());
                default: return getNewRelationName(atom->getQualifiedName());
            }
        }

        if (isRecursive()) {
            if (sccAtoms.at(version + 1) == atom) {
                return getDeltaRelationName(atom->getQualifiedName());
            }
        }
    }
    */

    if (!isRecursive()) {
        assert(mode != IncrementalUpdatedDiffMinus && mode != IncrementalUpdatedDiffPlus && "mode shouldn't be IncrementalUpdated for non-recursive rules");

        if (ast::getBodyLiterals<ast::Atom>(clause).at(diffVersion) == atom) {
            if (mode == IncrementalDiffPlus) {
                return getActualDiffPlusRelationName(atom->getQualifiedName());
            } else if (mode == IncrementalDiffMinus) {
                return getActualDiffMinusRelationName(atom->getQualifiedName());
            }
        }

        if (clause.getHead() == atom) {
            if (mode == IncrementalDiffPlus) {
                return getDiffPlusRelationName(atom->getQualifiedName());
            } else if (mode == IncrementalDiffMinus) {
                return getDiffMinusRelationName(atom->getQualifiedName());
            }
        }

        if (mode == IncrementalDiffPlus) {
            return getConcreteRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalDiffMinus) {
            return getPrevRelationName(atom->getQualifiedName());
        }
    }

    if (clause.getHead() == atom) {
        if (mode == IncrementalDiffMinus || mode == IncrementalUpdatedDiffPlus) {
            return getNewDiffMinusRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalDiffPlus || mode == IncrementalUpdatedDiffMinus) {
            return getNewDiffPlusRelationName(atom->getQualifiedName());
        }
    }

    if (ast::getBodyLiterals<ast::Atom>(clause).at(diffVersion) == atom) {
        if (mode == IncrementalDiffPlus) {
            return getActualDiffPlusRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalDiffMinus) {
            return getActualDiffMinusRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalUpdatedDiffPlus) {
            return getUpdatedDiffPlusRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalUpdatedDiffMinus) {
            return getUpdatedDiffMinusRelationName(atom->getQualifiedName());
        }
    }

    if (mode == IncrementalDiffPlus || mode == IncrementalUpdatedDiffMinus) {
        return getConcreteRelationName(atom->getQualifiedName());
    } else if (mode == IncrementalDiffMinus || mode == IncrementalUpdatedDiffPlus) {
        return getPrevRelationName(atom->getQualifiedName());
    }

    return getConcreteRelationName(atom->getQualifiedName());
}

Own<ram::Operation> ClauseTranslator::addNegatedAtom(
        Own<ram::Operation> op, const ast::Clause& /* clause */, const ast::Atom* /* atom */) const {
    /*
    VecOwn<ram::Expression> values;

    auto args = atom->getArguments();
    for (const auto* arg : args) {
        values.push_back(context.translateValue(*valueIndex, arg));
    }

    // undefined value for rule number
    values.push_back(mk<ram::UndefValue>());

    // height
    // TODO: i need to work out what this is lol
    values.push_back(mk<ram::UndefValue>());

    return mk<ram::Filter>(mk<ram::Negation>(mk<ram::ProvenanceExistenceCheck>(
                                   getConcreteRelationName(atom->getQualifiedName()), std::move(values))),
            std::move(op));
            */

    return op;
}

Own<ram::Operation> ClauseTranslator::addBodyLiteralConstraints(
        const ast::Clause& clause, Own<ram::Operation> op) const {

    op = ast2ram::seminaive::ClauseTranslator::addBodyLiteralConstraints(clause, std::move(op));

    // For incremental update, ensure that all tuples are correctly existing/not-existing
    for (std::size_t i = 0; i < getAtomOrdering(clause).size(); i++) {
        const auto* atom = getAtomOrdering(clause)[i];

        if (mode == IncrementalDiffMinus && i == diffVersion) {
            op = mk<ram::Filter>(mk<ram::Constraint>(BinaryConstraintOp::LT,
                        mk<ram::TupleElement>(i, atom->getArity() + 1),
                        mk<ram::SignedConstant>(0)),
                    std::move(op));
        } else {
            op = mk<ram::Filter>(mk<ram::Constraint>(BinaryConstraintOp::GT,
                        mk<ram::TupleElement>(i, atom->getArity() + 1),
                        mk<ram::SignedConstant>(0)),
                    std::move(op));
        }
    }

    // For recursion, ensure that atoms before position 'version' have iter <
    // current iter, and atoms after have iter <= current iter
    if (isRecursive()) {
        for (std::size_t i = 0; i < getAtomOrdering(clause).size(); i++) {
            const auto* atom = getAtomOrdering(clause)[i];

            // check if atom is before or after version
            // if atom is equal to version, or if it is non-recursive, before
            // and after will both be false
            bool before = false;
            bool after = false;
            for (std::size_t j = 0; j < sccAtoms.size(); j++) {
                if (*sccAtoms[j] == *atom) {
                    if (j < version) {
                        before = true;
                    } else if (j > version) {
                        after = true;
                    }
                    break;
                }
            }

            VecOwn<ram::Expression> iterMinusOneArgs;
            iterMinusOneArgs.push_back(mk<ram::IterationNumber>());
            iterMinusOneArgs.push_back(mk<ram::SignedConstant>(1));

            auto iterMinusOne = mk<ram::IntrinsicOperator>(FunctorOp::SUB, std::move(iterMinusOneArgs));

            if (before) {
                op = mk<ram::Filter>(mk<ram::Constraint>(BinaryConstraintOp::LT,
                            mk<ram::TupleElement>(i, atom->getArity()),
                            std::move(iterMinusOne)),
                        std::move(op));
            } else if (after) {
                op = mk<ram::Filter>(mk<ram::Constraint>(BinaryConstraintOp::LE,
                            mk<ram::TupleElement>(i, atom->getArity()),
                            std::move(iterMinusOne)),
                        std::move(op));
            }
        }
    }

    std::size_t lastScanLevel = 0;
    while (valueIndex->isSomethingDefinedOn(lastScanLevel)) {
        lastScanLevel++;
    }

    // For some body tuples, we need to ensure the same tuple exists in both R
    // and prev_R
    std::size_t tupleExistsLevel = lastScanLevel;
    for (std::size_t i = 0; i < diffVersion; i++) {
        // TODO: check how getAtomOrdering works with diffVersions
        const auto* atom = getAtomOrdering(clause)[i];

        std::string checkRelation;

        if (mode == IncrementalDiffPlus || mode == IncrementalUpdatedDiffMinus) {
            checkRelation = getPrevRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalDiffMinus || mode == IncrementalUpdatedDiffPlus) {
            checkRelation = getConcreteRelationName(atom->getQualifiedName());
        }

        op = addEnsureExistsInRelationConstraint(std::move(op), atom, checkRelation, tupleExistsLevel);

        tupleExistsLevel++;
    }

    lastScanLevel = tupleExistsLevel;

    // For some body tuples, we need to ensure the tuple for the rule
    // evaluation is the earliest one in its relation

    // atomIdx keeps track of which atom we are creating a constraint for
    std::size_t atomIdx = 0;

    std::size_t iterCheckLevel = lastScanLevel;
    for (const auto* atom : getAtomOrdering(clause)) {
        if (atomIdx == diffVersion && (mode == IncrementalUpdatedDiffPlus || mode == IncrementalUpdatedDiffMinus)) {
            continue;
        }

        std::string checkRelation;

        if (mode == IncrementalDiffPlus || mode == IncrementalUpdatedDiffPlus) {
            checkRelation = getConcreteRelationName(atom->getQualifiedName());
        } else if (mode == IncrementalDiffMinus || mode == IncrementalUpdatedDiffMinus) {
            checkRelation = getPrevRelationName(atom->getQualifiedName());
        }

        op = addEnsureEarliestIterationConstraint(std::move(op), atom, iterCheckLevel, checkRelation, atomIdx);

        atomIdx++;
        iterCheckLevel++;
    }

    lastScanLevel = iterCheckLevel;

    // For deleting tuples, we must ensure that the tuple actually exists for deletion
    if (mode == IncrementalUpdatedDiffPlus || mode == IncrementalDiffMinus) {
        op = addEnsureExistsForDeletionConstraint(std::move(op), clause.getHead(), lastScanLevel);
    }

    return op;
}

Own<ram::Operation> ClauseTranslator::addEnsureExistsInRelationConstraint(Own<ram::Operation> op, const ast::Atom* atom, std::string checkRelation, std::size_t curLevel) const {
    // For incremental update, ensure that some body tuples exist in both the
    // previous and current epochs to prevent double counting. For example,
    // consider the rule
    //
    //   R :- S, T.
    //
    // This generates two diff versions
    //
    //   diff_minus_R :- diff_minus_S, prev_T.
    //   diff_minus_R :- prev_S, diff_minus_T.
    //
    // We need to ensure that for the second case, the tuple for prev_S also
    // exists in S, otherwise it would be double counting tuples in S that are
    // removed. To achieve this, add an extra existence check:
    //
    //   FOR t0 in prev_S:
    //     FOR t1 in diff_minus_T:
    //       IF EXISTS t0 in S WHERE t0.count > 0
    //         ...

    // First create a filter condition saying the count must be positive
    Own<ram::Condition> tupleExistsCond = mk<ram::Constraint>(BinaryConstraintOp::GT, mk<ram::TupleElement>(curLevel, atom->getArity() + 1), mk<ram::SignedConstant>(0));

    // Add a condition saying the iteration number must be earlier than current iter
    tupleExistsCond = addConjunctiveTerm(std::move(tupleExistsCond), mk<ram::Constraint>(BinaryConstraintOp::LE, mk<ram::TupleElement>(curLevel, atom->getArity()), mk<ram::IterationNumber>()));

    // Add conditions to say the tuple must match
    std::size_t argNum = 0;
    for (auto* arg : atom->getArguments()) {
        tupleExistsCond = addConjunctiveTerm(std::move(tupleExistsCond), mk<ram::Constraint>(BinaryConstraintOp::EQ, context.translateValue(*valueIndex, arg), mk<ram::TupleElement>(curLevel, argNum)));
        argNum++;
    }

    // Create a filter
    op = mk<ram::Filter>(std::move(tupleExistsCond), std::move(op));

    // Create a scan
    op = mk<ram::Scan>(checkRelation, curLevel, std::move(op));

    return op;
}

Own<ram::Operation> ClauseTranslator::addEnsureEarliestIterationConstraint(Own<ram::Operation> op, const ast::Atom* atom, std::size_t curLevel, std::string checkRelation, std::size_t atomIdx) const {
    // Ensure that we only compute using the earliest iteration for any given
    // tuple. For example, given a binary relation (x,y,@iter,@count), if we
    // have two tuples (1,2,3,1) and (1,2,5,1), we should only execute a rule
    // evaluation for the earliest tuple (1,2,3,1), otherwise incremental
    // evaluation double counts.

    // Add a constraint saying that iter = ITERNUM() - 1 for the current
    // version atom, simulating delta of semi-naive
    if (isRecursive() && sccAtoms.at(version) == atom) {
        VecOwn<ram::Expression> iterMinusOneArgs;
        iterMinusOneArgs.push_back(mk<ram::IterationNumber>());
        iterMinusOneArgs.push_back(mk<ram::SignedConstant>(1));

        auto iterMinusOne = mk<ram::IntrinsicOperator>(FunctorOp::SUB, std::move(iterMinusOneArgs));

        op = mk<ram::Filter>(mk<ram::Constraint>(BinaryConstraintOp::EQ, mk<ram::TupleElement>(atomIdx, atom->getArity()), std::move(iterMinusOne)), std::move(op));
    }

    // Make conditions
    // Make count condition, i.e., c > 0 in above example
    Own<ram::Condition> cond = mk<ram::Constraint>(BinaryConstraintOp::GT, mk<ram::TupleElement>(curLevel, atom->getArity() + 1), mk<ram::SignedConstant>(0));

    // Make iteration condition, i.e., iter < current iter
    cond = addConjunctiveTerm(std::move(cond), mk<ram::Constraint>(BinaryConstraintOp::LT, mk<ram::TupleElement>(curLevel, atom->getArity()), mk<ram::TupleElement>(atomIdx, atom->getArity())));

    // Add conditions such that X... inside ifnotexists is equal to outside
    std::size_t argNum = 0;
    for (auto* arg : atom->getArguments()) {
        cond = addConjunctiveTerm(std::move(cond), mk<ram::Constraint>(BinaryConstraintOp::EQ, context.translateValue(*valueIndex, arg), mk<ram::TupleElement>(curLevel, argNum)));
        argNum++;
    }

    std::string relName;

    op = mk<ram::IfNotExists>(checkRelation, curLevel, std::move(cond), std::move(op));

    return op;
}

Own<ram::Operation> ClauseTranslator::addEnsureExistsForDeletionConstraint(Own<ram::Operation> op, const ast::Atom* atom, std::size_t curLevel) const {
    // For incremental update, when an incremental deletion occurs, we must
    // ensure that the corresponding tuple actually exists in the relation so
    // we can delete it.

    // First create a filter condition saying the count must be positive
    Own<ram::Condition> tupleExistsCond = mk<ram::Constraint>(BinaryConstraintOp::GT, mk<ram::TupleElement>(curLevel, atom->getArity() + 1), mk<ram::SignedConstant>(0));

    // Add a condition saying the iteration number must be equal to current iter
    tupleExistsCond = addConjunctiveTerm(std::move(tupleExistsCond), mk<ram::Constraint>(BinaryConstraintOp::EQ, mk<ram::TupleElement>(curLevel, atom->getArity()), mk<ram::IterationNumber>()));

    // Add conditions to say the tuple must match
    std::size_t argNum = 0;
    for (auto* arg : atom->getArguments()) {
        tupleExistsCond = addConjunctiveTerm(std::move(tupleExistsCond), mk<ram::Constraint>(BinaryConstraintOp::EQ, context.translateValue(*valueIndex, arg), mk<ram::TupleElement>(curLevel, argNum)));
        argNum++;
    }

    // Create a filter
    op = mk<ram::Filter>(std::move(tupleExistsCond), std::move(op));

    // Create a scan
    op = mk<ram::Scan>(getConcreteRelationName(atom->getQualifiedName()), curLevel, std::move(op));

    return op;
}

void ClauseTranslator::indexAtoms(const ast::Clause& clause) {
    std::size_t atomIdx = 0;
    for (const auto* atom : getAtomOrdering(clause)) {
        // give the atom the current level
        int scanLevel = addOperatorLevel(atom);
        indexNodeArguments(scanLevel, atom->getArguments());

        // Add rule num variable
        std::string iterationNumVarName = "@iteration_" + std::to_string(atomIdx);
        valueIndex->addVarReference(iterationNumVarName, scanLevel, atom->getArity());

        // Add level num variable
        std::string countNumVarName = "@count_" + std::to_string(atomIdx);
        valueIndex->addVarReference(countNumVarName, scanLevel, atom->getArity() + 1);

        atomIdx++;
    }
}

Own<ram::Expression> ClauseTranslator::getLevelNumber(const ast::Clause& clause) const {
    auto getLevelVariable = [&](std::size_t atomIdx) { return "@level_num_" + std::to_string(atomIdx); };

    const auto& bodyAtoms = getAtomOrdering(clause);
    if (bodyAtoms.empty()) return mk<ram::SignedConstant>(0);

    VecOwn<ram::Expression> values;
    for (std::size_t i = 0; i < bodyAtoms.size(); i++) {
        auto levelVar = mk<ast::Variable>(getLevelVariable(i));
        values.push_back(context.translateValue(*valueIndex, levelVar.get()));
    }
    assert(!values.empty() && "unexpected empty value set");

    auto maxLevel = values.size() == 1 ? std::move(values.at(0))
                                       : mk<ram::IntrinsicOperator>(FunctorOp::MAX, std::move(values));

    VecOwn<ram::Expression> addArgs;
    addArgs.push_back(std::move(maxLevel));
    addArgs.push_back(mk<ram::SignedConstant>(1));
    return mk<ram::IntrinsicOperator>(FunctorOp::ADD, std::move(addArgs));
}

Own<ram::Operation> ClauseTranslator::addAtomScan(
        Own<ram::Operation> op, const ast::Atom* atom, const ast::Clause& clause, std::size_t curLevel) const {
    // add constraints
    op = addConstantConstraints(curLevel, atom->getArguments(), std::move(op));

    // add check for emptiness for an atom
    op = mk<ram::Filter>(
            mk<ram::Negation>(mk<ram::EmptinessCheck>(getClauseAtomName(clause, atom))), std::move(op));

    // add a scan level
    std::stringstream ss;
    if (Global::config().has("profile")) {
        ss << "@frequency-atom" << ';';
        ss << clause.getHead()->getQualifiedName() << ';';
        ss << version << ';';
        ss << stringify(getClauseString(clause)) << ';';
        ss << stringify(getClauseAtomName(clause, atom)) << ';';
        ss << stringify(toString(clause)) << ';';
        ss << curLevel << ';';
    }
    op = mk<ram::Scan>(getClauseAtomName(clause, atom), curLevel, std::move(op), ss.str());

    return op;
}

Own<ram::Operation> ClauseTranslator::createInsertion(const ast::Clause& clause) const {
    const auto head = clause.getHead();
    auto headRelationName = getClauseAtomName(clause, head);

    VecOwn<ram::Expression> values;
    for (const auto* arg : head->getArguments()) {
        values.push_back(context.translateValue(*valueIndex, arg));
    }

    // add rule number + level number
    if (isFact(clause)) {
        values.push_back(mk<ram::SignedConstant>(0));
        values.push_back(mk<ram::SignedConstant>(0));
    } else {
        values.push_back(mk<ram::IterationNumber>());
        if (mode == IncrementalDiffPlus || mode == IncrementalUpdatedDiffMinus) {
            values.push_back(mk<ram::SignedConstant>(1));
        } else if (mode == IncrementalDiffMinus || mode == IncrementalUpdatedDiffPlus) {
            values.push_back(mk<ram::SignedConstant>(-1));
        } else {
            std::cerr << "incremental update translate mode should be either diff_plus or diff_minus, never default" << std::endl;
            values.push_back(mk<ram::SignedConstant>(1));
        }
    }

    // Relations with functional dependency constraints
    if (auto guardedConditions = getFunctionalDependencies(clause)) {
        return mk<ram::GuardedInsert>(headRelationName, std::move(values), std::move(guardedConditions));
    }

    // Everything else
    return mk<ram::Insert>(headRelationName, std::move(values));
}

}  // namespace souffle::ast2ram::incremental::update
