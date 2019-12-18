/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ProvenanceTransformer.cpp
 *
 * Implements AstTransformer for adding provenance information via two extra columns
 *
 ***********************************************************************/

#include "AstArgument.h"
#include "AstAttribute.h"
#include "AstClause.h"
#include "AstLiteral.h"
#include "AstNode.h"
#include "AstProgram.h"
#include "AstRelation.h"
#include "AstRelationIdentifier.h"
#include "AstTransforms.h"
#include "AstTranslationUnit.h"
#include "AstType.h"
#include "AstVisitor.h"
#include "BinaryConstraintOps.h"
#include "FunctorOps.h"
#include "RelationRepresentation.h"
#include "Util.h"
#include <cassert>
#include <cstddef>
#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

namespace souffle {

/**
 * Adds unnamed variables to each atom
 * Intended to be used inside negations and constraints
 */
struct addUnnamedVariables : public AstNodeMapper {
    using AstNodeMapper::operator();

    std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
        // add provenance columns
        if (auto atom = dynamic_cast<AstAtom*>(node.get())) {
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
        } else if (auto neg = dynamic_cast<AstNegation*>(node.get())) {
            auto atom = neg->getAtom();
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
        } else if (auto agg = dynamic_cast<AstAggregator*>(node.get())) {
            if (auto innerVar = dynamic_cast<const AstVariable*>(agg->getTargetExpression())) {
                if (innerVar->getName() == "@current_epoch_value") {
                    return node;
                }
            }
        }

        // otherwise - apply mapper recursively
        node->apply(*this);
        return node;
    }
};

// apply a functor to a list of vars
AstArgument* applyFunctorToVars(std::vector<AstArgument*> levels, FunctorOp op) {
    if (levels.empty()) {
        return static_cast<AstArgument*>(new AstNumberConstant(0));
    }

    if (levels.size() == 1) {
        return static_cast<AstArgument*>(levels[0]);
    }

    auto currentCombination = new AstIntrinsicFunctor(op, std::unique_ptr<AstArgument>(levels[0]),
            std::unique_ptr<AstArgument>(levels[1]));

    for (size_t i = 2; i < levels.size(); i++) {
        currentCombination = new AstIntrinsicFunctor(op, std::unique_ptr<AstArgument>(currentCombination),
                std::unique_ptr<AstArgument>(levels[i]));
    }

    return static_cast<AstArgument*>(currentCombination);
};

/**
 * This transforms a clause to process tuple deletions
 */
std::unique_ptr<AstClause> IncrementalTransformer::makeNegativeUpdateClause(const AstClause& clause) {
    // make a clone of the clause
    auto negativeUpdateClause = clause.clone();

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    std::vector<AstArgument*> bodyPreviousCounts;
    std::vector<AstArgument*> bodyCountDiffs;
    std::vector<AstArgument*> bodyCounts;

    for (size_t i = 0; i < negativeUpdateClause->getBodyLiterals().size(); i++) {

        auto lit = negativeUpdateClause->getBodyLiterals()[i];

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
            bodyPreviousCounts.push_back(new AstVariable("@prev_count_" + std::to_string(i)));
            bodyCountDiffs.push_back(new AstIntrinsicFunctor(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i))));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    negativeUpdateClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));

    // second is the previous epoch's count, which we set to 0 signifying that we are updating the head tuple
    negativeUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));

    // third is the current epoch's count, which we set to -1, triggering a decrement in the count
    negativeUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(-1));

    // add constraint to the rule saying that all body tuples must have existed prior,
    // i.e. tuples that are deleted in prior epochs shouldn't be deleted again
    negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyPreviousCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    // add constraint to the rule saying that at least one body atom must have been updated in the current epoch
    // we do this by doing min(count_cur_1 - count_prev_1, count_cur_2 - count_prev_2, ...) < 0
    negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCountDiffs, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    // add constraint to the rule saying that at least one body atom must have negative count
    negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    return std::unique_ptr<AstClause>(negativeUpdateClause);
}

/**
 * This transforms a clause to process tuple additions
 */
std::unique_ptr<AstClause> IncrementalTransformer::makePositiveUpdateClause(const AstClause& clause) {
    // make a clone of the clause
    auto positiveUpdateClause = clause.clone();

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    std::vector<AstArgument*> bodyCountDiffs;
    std::vector<AstArgument*> bodyCounts;

    for (size_t i = 0; i < positiveUpdateClause->getBodyLiterals().size(); i++) {

        auto lit = positiveUpdateClause->getBodyLiterals()[i];

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));

            // TODO: comment this properly, it's really messed up
            // basically we want to encode 1 if (diff > 0 && prev_count == 0), 0 otherwise
            // we do this by (BNOT(prev_count BOR 0) LAND (count - prev_count))
            bodyCountDiffs.push_back((new AstIntrinsicFunctor(FunctorOp::LAND, 
                            (std::make_unique<AstIntrinsicFunctor>(FunctorOp::LNOT, std::make_unique<AstIntrinsicFunctor>(FunctorOp::BOR, std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)), std::make_unique<AstNumberConstant>(0)))),
                            (std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)))))));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    positiveUpdateClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));

    // second is the previous epoch's count, which we set to 0, signifying that we are updating the head tuple
    positiveUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));

    // third is the current epoch's count, which we set to 1, triggering an increment in the count
    positiveUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    // add constraint to the rule saying that at least one body atom must have been updated in the current epoch
    // we do this by doing max(count_cur_1 - count_prev_1, count_cur_2 - count_prev_2, ...) > 0
    positiveUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCountDiffs, FunctorOp::MAX)),
                std::make_unique<AstNumberConstant>(0)));

    // add constraint to the rule saying that all body atoms must have positive count
    positiveUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    return std::unique_ptr<AstClause>(positiveUpdateClause);
}

/**
 * This transforms a clause to process generation of new tuples in an epoch after the body tuples are already stable
 */
std::unique_ptr<AstClause> IncrementalTransformer::makePositiveGenerationClause(const AstClause& clause) {
    // make a clone of the clause
    auto positiveGenerationClause = clause.clone();

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    std::vector<AstArgument*> bodyCountDiffs;
    std::vector<AstArgument*> bodyCounts;

    for (size_t i = 0; i < positiveGenerationClause->getBodyLiterals().size(); i++) {

        auto lit = positiveGenerationClause->getBodyLiterals()[i];

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
            bodyCountDiffs.push_back(new AstIntrinsicFunctor(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i))));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    positiveGenerationClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));

    // second is the previous epoch's count, which we set to 1, signifying that this tuple should have always existed, but was not generated in a prior epoch for some other reason
    positiveGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    // third is the current epoch's count, which we set to 1, inserting a new tuple with positive count
    positiveGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    // add constraint to the rule saying that at least one body atom must have been updated in the current epoch
    // we do this by doing min(count_cur_1 - count_prev_1, count_cur_2 - count_prev_2, ...) > 0
    for (auto bodyCountDiff : bodyCountDiffs) {
        positiveGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ, std::unique_ptr<AstArgument>(bodyCountDiff), std::make_unique<AstNumberConstant>(0)));
    }

    // add constraint to the rule saying that all body atoms must have positive count
    positiveGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    return std::unique_ptr<AstClause>(positiveGenerationClause);
}

bool IncrementalTransformer::transform(AstTranslationUnit& translationUnit) {
    auto program = translationUnit.getProgram();

    std::cout << "before:\n";
    program->print(std::cout);
    std::cout << std::endl;

    /*
    // get next level number
    auto getNextLevelNumber = [&](std::vector<AstArgument*> levels) {
        if (levels.empty()) {
            return static_cast<AstArgument*>(new AstNumberConstant(0));
        }

        if (levels.size() == 1) {
            return static_cast<AstArgument*>(new AstIntrinsicFunctor(FunctorOp::ADD,
                    std::unique_ptr<AstArgument>(levels[0]), std::make_unique<AstNumberConstant>(1)));
        }

        auto currentMax = new AstIntrinsicFunctor(FunctorOp::MAX, std::unique_ptr<AstArgument>(levels[0]),
                std::unique_ptr<AstArgument>(levels[1]));

        for (size_t i = 2; i < levels.size(); i++) {
            currentMax = new AstIntrinsicFunctor(FunctorOp::MAX, std::unique_ptr<AstArgument>(currentMax),
                    std::unique_ptr<AstArgument>(levels[i]));
        }

        return static_cast<AstArgument*>(new AstIntrinsicFunctor(FunctorOp::ADD,
                std::unique_ptr<AstArgument>(currentMax), std::make_unique<AstNumberConstant>(1)));
    };

    // get min body counts
    auto combineBodyCounts = [&](std::vector<AstArgument*> levels, FunctorOp op) {
        if (levels.empty()) {
            return static_cast<AstArgument*>(new AstNumberConstant(0));
        }

        if (levels.size() == 1) {
            return static_cast<AstArgument*>(levels[0]);
        }

        auto currentComb = new AstIntrinsicFunctor(op, std::unique_ptr<AstArgument>(levels[0]),
                std::unique_ptr<AstArgument>(levels[1]));

        for (size_t i = 2; i < levels.size(); i++) {
            currentComb = new AstIntrinsicFunctor(op, std::unique_ptr<AstArgument>(currentComb),
                    std::unique_ptr<AstArgument>(levels[i]));
        }

        return static_cast<AstArgument*>(currentComb);
    };
    */

    // go through each relation and its rules to add annotations
    for (auto relation : program->getRelations()) {
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@iteration"), AstTypeIdentifier("number")));
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@prev_count"), AstTypeIdentifier("number")));
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@current_count"), AstTypeIdentifier("number")));

        /*
        struct M : public AstNodeMapper {
            using AstNodeMapper::operator();

            std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
                // add provenance columns
                if (auto atom = dynamic_cast<AstAtom*>(node.get())) {
                    atom->addArgument(std::make_unique<AstUnnamedVariable>());
                    atom->addArgument(std::make_unique<AstUnnamedVariable>());
                } else if (auto neg = dynamic_cast<AstNegation*>(node.get())) {
                    auto atom = neg->getAtom();
                    atom->addArgument(std::make_unique<AstUnnamedVariable>());
                    atom->addArgument(std::make_unique<AstUnnamedVariable>());
                } else if (auto agg = dynamic_cast<AstAggregator*>(node.get())) {
                    if (auto innerVar = dynamic_cast<const AstVariable*>(agg->getTargetExpression())) {
                        if (innerVar->getName() == "@current_epoch_value") {
                            return node;
                        }
                    }
                }

                // otherwise - apply mapper recursively
                node->apply(*this);
                return node;
            }
        };
        */

        /*
        // create aggregator that ensures the current epoch is being processed
        auto maxEpochBodyLiteral = std::make_unique<AstAtom>(AstRelationIdentifier("+current_epoch"));
        maxEpochBodyLiteral->addArgument(std::make_unique<AstVariable>("@current_epoch_value"));
        auto maxEpochAggregator = std::make_unique<AstAggregator>(AstAggregator::Op::max);
        maxEpochAggregator->addBodyLiteral(std::move(maxEpochBodyLiteral));
        maxEpochAggregator->setTargetExpression(std::make_unique<AstVariable>("@current_epoch_value"));
        */

        // store a list of original clauses in the relation, to be deleted
        std::vector<AstClause*> originalClauses;

        for (auto clause : relation->getClauses()) {
            // mapper to add two provenance columns to atoms
            // add unnamed vars to each atom nested in arguments of head
            clause->getHead()->apply(addUnnamedVariables());

            // if fact, level number is 0
            if (clause->isFact()) {
                clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
                clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
                clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));
            } else {
                relation->addClause(std::unique_ptr<AstClause>(makeNegativeUpdateClause(*clause)));
                relation->addClause(std::unique_ptr<AstClause>(makePositiveUpdateClause(*clause)));
                relation->addClause(std::unique_ptr<AstClause>(makePositiveGenerationClause(*clause)));

                originalClauses.push_back(clause);
            }
        }

        // delete original clauses once instrumented clauses are added
        for (auto clause : originalClauses) {
            relation->removeClause(clause);
        }
    }

    /*
    // add a relation for the current epoch number
    auto epochRelation = std::make_unique<AstRelation>();
    // use + because @ is explicitly reserved for temporary (new and delta) relations
    epochRelation->setName(AstRelationIdentifier("+current_epoch"));
    epochRelation->addAttribute(std::make_unique<AstAttribute>("@epoch", AstTypeIdentifier("number")));
    // add a single fact to epochRelation
    auto epochRelationFact = std::make_unique<AstAtom>(AstRelationIdentifier("+current_epoch"));
    epochRelationFact->addArgument(std::make_unique<AstNumberConstant>(0));

    auto epochRelationClause = std::make_unique<AstClause>();
    epochRelationClause->setHead(std::move(epochRelationFact));
    epochRelation->addClause(std::move(epochRelationClause));
    epochRelation->setQualifier(OUTPUT_RELATION);

    program->addRelation(std::move(epochRelation));
    */

    std::cout << "after:\n";
    program->print(std::cout);
    std::cout << std::endl;
    return true;
}

}  // end of namespace souffle
