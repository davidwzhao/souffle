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

bool IncrementalTransformer::transform(AstTranslationUnit& translationUnit) {
    auto program = translationUnit.getProgram();

    /*
    std::cout << "before:\n";
    program->print(std::cout);
    std::cout << std::endl;
    */

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

    // go through each relation and its rules to add annotations
    for (auto relation : program->getRelations()) {
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@iteration"), AstTypeIdentifier("number")));
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@epoch"), AstTypeIdentifier("number")));
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@count"), AstTypeIdentifier("number")));

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

        // create aggregator that ensures the current epoch is being processed
        auto maxEpochBodyLiteral = std::make_unique<AstAtom>(AstRelationIdentifier("+current_epoch"));
        maxEpochBodyLiteral->addArgument(std::make_unique<AstVariable>("@current_epoch_value"));
        auto maxEpochAggregator = std::make_unique<AstAggregator>(AstAggregator::Op::max);
        maxEpochAggregator->addBodyLiteral(std::move(maxEpochBodyLiteral));
        maxEpochAggregator->setTargetExpression(std::make_unique<AstVariable>("@current_epoch_value"));

        for (auto clause : relation->getClauses()) {
            // mapper to add two provenance columns to atoms
            // add unnamed vars to each atom nested in arguments of head
            clause->getHead()->apply(M());

            // if fact, level number is 0
            if (clause->isFact()) {
                // clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
                // clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));
            } else {
                // make a clone of clause for negative update version
                auto negativeUpdateClause = clause->clone();

                // but first, process the normal version
                std::vector<AstArgument*> bodyEpochs;
                std::vector<AstArgument*> bodyLevels;

                for (size_t i = 0; i < clause->getBodyLiterals().size(); i++) {
                    auto lit = clause->getBodyLiterals()[i];

                    std::cout << "lit:\n";
                    lit->print(std::cout);
                    std::cout << std::endl;

                    // add unnamed vars to each atom nested in arguments of lit
                    lit->apply(M());

                    // add two provenance columns to lit; first is rule num, second is level num
                    if (auto atom = dynamic_cast<AstAtom*>(lit)) {
                        atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
                        atom->addArgument(std::make_unique<AstVariable>("@epoch_" + std::to_string(i)));
                        atom->addArgument(std::make_unique<AstVariable>("@count_" + std::to_string(i)));
                        bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
                        bodyEpochs.push_back(new AstVariable("@epoch_" + std::to_string(i)));
                        clause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                std::make_unique<AstVariable>("@count_" + std::to_string(i)),
                                std::make_unique<AstNumberConstant>(0)));
                    }
                }

                // add three incremental columns to head lit
                clause->getHead()->addArgument(std::unique_ptr<AstArgument>(getNextLevelNumber(bodyLevels)));
                clause->getHead()->addArgument(std::unique_ptr<AstAggregator>(maxEpochAggregator->clone()));
                clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

                clause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ, std::unique_ptr<AstArgument>(combineBodyCounts(bodyEpochs, FunctorOp::MAX)), std::unique_ptr<AstAggregator>(maxEpochAggregator->clone())));

                // now, process the negative update version
                std::vector<AstArgument*> negativeUpdateBodyEpochs;
                std::vector<AstArgument*> negativeUpdateBodyLevels;
                std::vector<AstArgument*> negativeUpdateBodyCounts;

                for (size_t i = 0; i < negativeUpdateClause->getBodyLiterals().size(); i++) {
                    auto lit = negativeUpdateClause->getBodyLiterals()[i];

                    // add unnamed vars to each atom nested in arguments of lit
                    lit->apply(M());

                    // add two provenance columns to lit; first is rule num, second is level num
                    if (auto atom = dynamic_cast<AstAtom*>(lit)) {
                        atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
                        atom->addArgument(std::make_unique<AstVariable>("@epoch_" + std::to_string(i)));
                        atom->addArgument(std::make_unique<AstVariable>("@count_" + std::to_string(i)));
                        negativeUpdateBodyLevels.push_back(
                                new AstVariable("@iteration_" + std::to_string(i)));
                        negativeUpdateBodyEpochs.push_back(new AstVariable("@epoch_" + std::to_string(i)));
                        negativeUpdateBodyCounts.push_back(new AstVariable("@count_" + std::to_string(i)));
                    }
                }

                // add three incremental columns to head lit
                negativeUpdateClause->getHead()->addArgument(
                        std::unique_ptr<AstArgument>(getNextLevelNumber(negativeUpdateBodyLevels)));
                negativeUpdateClause->getHead()->addArgument(std::unique_ptr<AstAggregator>(maxEpochAggregator->clone()));
                negativeUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(-1));

                // add constraint saying that at least one body atom must be negative
                negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                        std::unique_ptr<AstArgument>(combineBodyCounts(negativeUpdateBodyCounts, FunctorOp::MIN)),
                        std::make_unique<AstNumberConstant>(0)));

                negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ, std::unique_ptr<AstArgument>(combineBodyCounts(negativeUpdateBodyEpochs, FunctorOp::MAX)), std::unique_ptr<AstAggregator>(maxEpochAggregator->clone())));

                relation->addClause(std::unique_ptr<AstClause>(negativeUpdateClause));
            }
        }
    }

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

    std::cout << "after:\n";
    program->print(std::cout);
    std::cout << std::endl;
    return true;
}

}  // end of namespace souffle
