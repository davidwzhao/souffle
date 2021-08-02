/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved.
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IncrementalTransformer.cpp
 *
 * Implements AstTransformer for adding incremental information via two extra columns
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
#include "PrecedenceGraph.h"
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
            /*
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
            */
        } else if (auto neg = dynamic_cast<AstNegation*>(node.get())) {
            /*
            auto atom = neg->getAtom();
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
            atom->addArgument(std::make_unique<AstUnnamedVariable>());
            */
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

/**
 * Helper functions
 */
const std::string provIdentifierToString(const AstRelationIdentifier& name) {
    std::stringstream ss;
    ss << name;
    return ss.str();
}

inline AstRelationIdentifier provMakeRelationName(
        const AstRelationIdentifier& orig, const std::string& type, int num = -1) {
    AstRelationIdentifier newName(provIdentifierToString(orig));
    newName.append(type);
    if (num != -1) {
        newName.append((const std::string&)std::to_string(num));
    }

    return newName;
}

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
}

template <typename T>
std::vector<T*> vectorClone(std::vector<T*> orig) {
    std::vector<T*> clones;
    for (auto elem : orig) {
        clones.push_back(elem->clone());
    }
    return clones;
}

std::unique_ptr<AstRelation> makeProvInfoRelation(
        AstClause& originalClause, AstTranslationUnit& translationUnit) {
    AstRelationIdentifier name =
            provMakeRelationName(originalClause.getHead()->getName(), "@info", originalClause.getClauseNum());

    // initialise info relation
    auto infoRelation = new AstRelation();
    infoRelation->setName(name);

    // create new clause containing a single fact
    auto infoClause = new AstClause();
    auto infoClauseHead = new AstAtom();
    infoClauseHead->setName(name);

    infoRelation->addAttribute(std::make_unique<AstAttribute>("clause_num", AstTypeIdentifier("number")));
    infoClauseHead->addArgument(std::make_unique<AstNumberConstant>(originalClause.getClauseNum()));

    // add head relation as meta info
    std::vector<std::string> headVariables;

    // get all variables and aggregates in the head
    struct HeadArgumentGetter : public AstNodeMapper {
        std::vector<std::string>& headVariables;

        HeadArgumentGetter(std::vector<std::string>& headVariables) : headVariables(headVariables) {}

        std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
            if (const auto* var = dynamic_cast<const AstVariable*>(node.get())) {
                std::stringstream varName;
                var->print(varName);
                headVariables.push_back(varName.str());
            } else if (const auto* agg = dynamic_cast<const AstAggregator*>(node.get())) {
                std::stringstream aggStringRepresentation;
                agg->print(aggStringRepresentation);
                headVariables.push_back(aggStringRepresentation.str());
            } else {
                // apply mapper to children
                node->apply(*this);
            }

            return node;
        }
    };

    HeadArgumentGetter headArgGet(headVariables);
    originalClause.getHead()->apply(headArgGet);

    // join variables in the head with commas
    std::stringstream headVariableString;
    headVariableString << join(headVariables, ",");

    // add an attribute to infoRelation for the head of clause
    infoRelation->addAttribute(
            std::make_unique<AstAttribute>(std::string("head_vars"), AstTypeIdentifier("symbol")));
    infoClauseHead->addArgument(
            std::make_unique<AstStringConstant>(translationUnit.getSymbolTable(), headVariableString.str()));

    // add a counter marking aggregates
    int aggregateNumber = 0;

    // visit all body literals and add to info clause head
    for (size_t i = 0; i < originalClause.getBodyLiterals().size(); i++) {
        auto lit = originalClause.getBodyLiterals()[i];
        const AstAtom* atom = lit->getAtom();

        // add an attribute for atoms and binary constraints
        if (atom != nullptr || dynamic_cast<AstBinaryConstraint*>(lit) != nullptr) {
            infoRelation->addAttribute(std::make_unique<AstAttribute>(
                    std::string("rel_") + std::to_string(i), AstTypeIdentifier("symbol")));
        }

        if (atom != nullptr) {
            std::string relName = provIdentifierToString(atom->getName());

            // for an atom, add its name and variables (converting aggregates to variables)
            if (dynamic_cast<AstAtom*>(lit) != nullptr) {
                std::string atomDescription = relName;

                for (auto& arg : atom->getArguments()) {
                    if (dynamic_cast<AstVariable*>(arg)) {
                        std::stringstream argDescription;
                        arg->print(argDescription);
                        atomDescription.append("," + argDescription.str());
                    } else if (dynamic_cast<AstAggregator*>(arg)) {
                        atomDescription.append(",agg_" + std::to_string(aggregateNumber++));
                    }
                }

                infoClauseHead->addArgument(std::make_unique<AstStringConstant>(
                        translationUnit.getSymbolTable(), atomDescription));
                // for a negation, add a marker with the relation name
            } else if (dynamic_cast<AstNegation*>(lit) != nullptr) {
                infoClauseHead->addArgument(std::make_unique<AstStringConstant>(
                        translationUnit.getSymbolTable(), ("!" + relName)));
            }
            // for a constraint, add the constraint symbol and LHS and RHS
        } else if (auto con = dynamic_cast<AstBinaryConstraint*>(lit)) {
            std::string constraintDescription = toBinaryConstraintSymbol(con->getOperator());

            if (auto var = dynamic_cast<AstVariable*>(con->getLHS())) {
                std::stringstream argDescription;
                var->print(argDescription);
                constraintDescription.append("," + argDescription.str());
            } else if (dynamic_cast<AstAggregator*>(con->getLHS())) {
                constraintDescription.append(",agg_" + std::to_string(aggregateNumber++));
            }

            if (auto var = dynamic_cast<AstVariable*>(con->getRHS())) {
                std::stringstream argDescription;
                var->print(argDescription);
                constraintDescription.append("," + argDescription.str());
            } else if (dynamic_cast<AstAggregator*>(con->getRHS())) {
                constraintDescription.append(",agg_" + std::to_string(aggregateNumber++));
            }

            infoClauseHead->addArgument(std::make_unique<AstStringConstant>(
                    translationUnit.getSymbolTable(), constraintDescription));
        }
    }

    // generate and add clause representation
    std::stringstream ss;
    originalClause.print(ss);

    infoRelation->addAttribute(std::make_unique<AstAttribute>("clause_repr", AstTypeIdentifier("symbol")));
    infoClauseHead->addArgument(
            std::make_unique<AstStringConstant>(translationUnit.getSymbolTable(), ss.str()));

    // set clause head and add clause to info relation
    infoClause->setHead(std::unique_ptr<AstAtom>(infoClauseHead));
    infoRelation->addClause(std::unique_ptr<AstClause>(infoClause));

    return std::unique_ptr<AstRelation>(infoRelation);
}

/**
 * This transforms a clause to process tuple deletions
 */
std::vector<AstClause*> IncrementalTransformer::makeNegativeUpdateClause(const AstClause& clause, const AstTranslationUnit& translationUnit) {
    // get the scc graph for generating iteration conditions
    const SCCGraph& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

    // make a clone of the clause
    auto negativeUpdateClause = clause.clone();

    // make vector of negativeUpdateClauses
    std::vector<AstClause*> negativeUpdateClauses;

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    // std::vector<AstArgument*> bodyPreviousCounts;
    // std::vector<AstArgument*> bodyCountDiffs;
    std::vector<AstArgument*> bodyCounts;

    // store number of atoms to be used for reordering
    size_t numAtoms = 0;

    for (size_t i = 0; i < negativeUpdateClause->getBodyLiterals().size(); i++) {

        auto lit = negativeUpdateClause->getBodyLiteral(i);

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            numAtoms++;

            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            // atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            // get relation of head atom
            auto headRelation = translationUnit.getProgram()->getRelation(clause.getHead()->getName());
            if (contains(sccGraph.getInternalRelations(sccGraph.getSCC(headRelation)), translationUnit.getProgram()->getRelation(atom->getName()))) {
                bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
            }
            // bodyPreviousCounts.push_back(new AstVariable("@prev_count_" + std::to_string(i)));
            // bodyCountDiffs.push_back(new AstIntrinsicFunctor(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i))));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
        } else if (auto neg = dynamic_cast<AstNegation*>(lit)) {

            // for negations, we don't care about iteration number or previous count
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(-1));
            // neg->getAtom()->addArgument(std::make_unique<AstUnnamedVariable>());

            // set current count to be 0, which signifies that we want to check that a tuple either doesn't exist, or exists with count of 0
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(0));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    // negativeUpdateClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));

    const RecursiveClauses& recursiveClauses = *translationUnit.getAnalysis<RecursiveClauses>();

    // first is the iteration number, which is counted inside each SCC
    if (recursiveClauses.recursive(&clause)) {
        negativeUpdateClause->getHead()->addArgument(std::make_unique<AstIterationNumber>());
    } else {
        negativeUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
    }

    // second is the previous epoch's count, which we set to 0 signifying that we are updating the head tuple
    // negativeUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    // third is the current epoch's count, which we set to -1, triggering a decrement in the count
    negativeUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(-1));

    /*
    // all tuples must have existed in prior iterations, i.e., tuples that are already deleted should not be deleted again
    negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyPreviousCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));
                */

    /*
    if (bodyLevels.size() > 0) {
        // add constraint to the rule saying that at least one body atom must have generated in the previous iteration
        negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX)),
                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
    }
    */

    /*
    // add constraint to the rule saying that at least one body atom must have negative count
    negativeUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));
                */

    negativeUpdateClauses.push_back(negativeUpdateClause);
    
    return negativeUpdateClauses;
}

/**
 * This transforms a clause to process tuple additions
 */
std::vector<AstClause*> IncrementalTransformer::makePositiveUpdateClause(const AstClause& clause, const AstTranslationUnit& translationUnit) {
    // get the scc graph for generating iteration conditions
    const SCCGraph& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

    // make a clone of the clause
    auto positiveUpdateClause = clause.clone();

    // make vector of positiveUpdateClauses
    std::vector<AstClause*> positiveUpdateClauses;

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    // std::vector<AstArgument*> bodyCountDiffs;
    // std::vector<AstArgument*> bodyPreviousCounts;
    std::vector<AstArgument*> bodyCounts;

    // store number of atoms to be used for reordering
    size_t numAtoms = 0;

    for (size_t i = 0; i < positiveUpdateClause->getBodyLiterals().size(); i++) {

        auto lit = positiveUpdateClause->getBodyLiterals()[i];

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            numAtoms++;

            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            // atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            // get relation of head atom
            auto headRelation = translationUnit.getProgram()->getRelation(clause.getHead()->getName());
            if (contains(sccGraph.getInternalRelations(sccGraph.getSCC(headRelation)), translationUnit.getProgram()->getRelation(atom->getName()))) {
                bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
            }

            // TODO: comment this properly, it's really messed up
            // basically we want to encode 1 if (diff > 0 && prev_count == 0), 0 otherwise
            // we do this by (BNOT(prev_count BOR 0) LAND (count - prev_count))
            /*
            bodyCountDiffs.push_back((new AstIntrinsicFunctor(FunctorOp::LAND, 
                            (std::make_unique<AstIntrinsicFunctor>(FunctorOp::LNOT, std::make_unique<AstIntrinsicFunctor>(FunctorOp::BOR, std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)), std::make_unique<AstNumberConstant>(0)))),
                            (std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)))))));
                            */
            // bodyPreviousCounts.push_back(new AstVariable("@prev_count_" + std::to_string(i)));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
        } else if (auto neg = dynamic_cast<AstNegation*>(lit)) {

            // for negations, we don't care about iteration number or previous count
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(-1));
            // neg->getAtom()->addArgument(std::make_unique<AstUnnamedVariable>());

            // set current count to be 0, which signifies that we want to check that a tuple either doesn't exist, or exists with count of 0
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(0));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    // positiveUpdateClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));

    const RecursiveClauses& recursiveClauses = *translationUnit.getAnalysis<RecursiveClauses>();

    // first is the iteration number, which is counted inside each SCC
    if (recursiveClauses.recursive(&clause)) {
        positiveUpdateClause->getHead()->addArgument(std::make_unique<AstIterationNumber>());
    } else {
        positiveUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
    }
    
    // second is the previous epoch's count, which we set to 0, signifying that we are updating the head tuple
    // positiveUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));

    // third is the current epoch's count, which we set to 1, triggering an increment in the count
    positiveUpdateClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    /*
    // all tuples must have existed in prior iterations, i.e., tuples that are already deleted should not be deleted again
    positiveUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));
                */

    /*
    if (bodyLevels.size() > 0) {
        // add constraint to the rule saying that at least one body atom must have generated in the previous iteration
        positiveUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX)),
                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
    }
    */

    /*
    // all tuples must have existed in prior iterations, i.e., tuples that are already deleted should not be deleted again
    positiveUpdateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyPreviousCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));
                */

    positiveUpdateClauses.push_back(positiveUpdateClause);
    return positiveUpdateClauses;
}

/**
 * This transforms a clause to process generation of new tuples in an epoch after the body tuples are already stable
 */
std::unique_ptr<AstClause> IncrementalTransformer::makeNegativeGenerationClause(const AstClause& clause, const AstTranslationUnit& translationUnit) {
    // get the scc graph for generating iteration conditions
    const SCCGraph& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

    // make a clone of the clause
    auto negativeGenerationClause = clause.clone();

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    // std::vector<AstArgument*> bodyCountDiffs;
    std::vector<AstArgument*> bodyCounts;
    // std::vector<AstArgument*> bodyPreviousCounts;

    // store number of atoms to be used for reordering
    size_t numAtoms = 0;

    for (size_t i = 0; i < negativeGenerationClause->getBodyLiterals().size(); i++) {

        auto lit = negativeGenerationClause->getBodyLiterals()[i];

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            numAtoms++;
            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            // atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            // get relation of head atom
            auto headRelation = translationUnit.getProgram()->getRelation(clause.getHead()->getName());
            if (contains(sccGraph.getInternalRelations(sccGraph.getSCC(headRelation)), translationUnit.getProgram()->getRelation(atom->getName()))) {
                bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
            }
            // bodyCountDiffs.push_back(new AstIntrinsicFunctor(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i))));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
            // bodyPreviousCounts.push_back(new AstVariable("@prev_count_" + std::to_string(i)));
        } else if (auto neg = dynamic_cast<AstNegation*>(lit)) {

            // for negations, we don't care about iteration number or previous count
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(-1));
            // neg->getAtom()->addArgument(std::make_unique<AstUnnamedVariable>());

            // set current count to be 0, which signifies that we want to check that a tuple either doesn't exist, or exists with count of 0
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(0));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    // negativeGenerationClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));
    
    const RecursiveClauses& recursiveClauses = *translationUnit.getAnalysis<RecursiveClauses>();

    // first is the iteration number, which is counted inside each SCC
    if (recursiveClauses.recursive(&clause)) {
        negativeGenerationClause->getHead()->addArgument(std::make_unique<AstIterationNumber>());
    } else {
        negativeGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
    }

    // second is the previous epoch's count, which we set to 1, signifying that this tuple should have always existed, but was not generated in a prior epoch for some other reason
    // negativeGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    // third is the current epoch's count, which we set to 1, inserting a new tuple with negative count
    // THE CONSTANT -2 IS A HACK!!:
    // this will be detected in the AstTranslator and an appropriate re-insertion rule will be generated
    negativeGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(-2));

    // add constraint to the rule saying that all body atoms must have negative count
    negativeGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    /*
    // add constraint to the rule saying that all body atoms must have previously existed
    negativeGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyPreviousCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));
                */

    /*
    if (bodyLevels.size() > 0) {
        // add constraint to the rule saying that at least one body atom must have generated in the previous iteration
        negativeGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX)),
                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
    }
    */

    return std::unique_ptr<AstClause>(negativeGenerationClause);
}

/**
 * This transforms a clause to process generation of new tuples in an epoch after the body tuples are already stable
 */
std::unique_ptr<AstClause> IncrementalTransformer::makePositiveGenerationClause(const AstClause& clause, const AstTranslationUnit& translationUnit) {
    // get the scc graph for generating iteration conditions
    const SCCGraph& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

    // make a clone of the clause
    auto positiveGenerationClause = clause.clone();

    // store the body counts to allow building arguments in the head atom
    std::vector<AstArgument*> bodyLevels;
    // std::vector<AstArgument*> bodyCountDiffs;
    std::vector<AstArgument*> bodyCounts;
    // std::vector<AstArgument*> bodyPreviousCounts;

    // store number of atoms to be used for reordering
    size_t numAtoms = 0;

    for (size_t i = 0; i < positiveGenerationClause->getBodyLiterals().size(); i++) {

        auto lit = positiveGenerationClause->getBodyLiterals()[i];

        // add unnamed vars to each atom nested in arguments of lit
        lit->apply(addUnnamedVariables());

        // add three incremental columns to lit; first is iteration number, second is count in previous epoch, third is count in current epoch
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            numAtoms++;
            atom->addArgument(std::make_unique<AstVariable>("@iteration_" + std::to_string(i)));
            // atom->addArgument(std::make_unique<AstVariable>("@prev_count_" + std::to_string(i)));
            atom->addArgument(std::make_unique<AstVariable>("@current_count_" + std::to_string(i)));
            
            // store the iterations and body counts to build arguments later
            // get relation of head atom
            auto headRelation = translationUnit.getProgram()->getRelation(clause.getHead()->getName());
            if (contains(sccGraph.getInternalRelations(sccGraph.getSCC(headRelation)), translationUnit.getProgram()->getRelation(atom->getName()))) {
                bodyLevels.push_back(new AstVariable("@iteration_" + std::to_string(i)));
            }
            // bodyCountDiffs.push_back(new AstIntrinsicFunctor(FunctorOp::SUB, std::make_unique<AstVariable>("@current_count_" + std::to_string(i)), std::make_unique<AstVariable>("@prev_count_" + std::to_string(i))));
            bodyCounts.push_back(new AstVariable("@current_count_" + std::to_string(i)));
            // bodyPreviousCounts.push_back(new AstVariable("@prev_count_" + std::to_string(i)));
        } else if (auto neg = dynamic_cast<AstNegation*>(lit)) {

            // for negations, we don't care about iteration number or previous count
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(-1));
            // neg->getAtom()->addArgument(std::make_unique<AstUnnamedVariable>());

            // set current count to be 0, which signifies that we want to check that a tuple either doesn't exist, or exists with count of 0
            neg->getAtom()->addArgument(std::make_unique<AstNumberConstant>(0));
        }
    }

    // add three incremental columns to head lit
    // first is the iteration number, which we get by adding 1 to the max iteration number over the body atoms
    // positiveGenerationClause->getHead()->addArgument(std::make_unique<AstIntrinsicFunctor>(FunctorOp::ADD, std::make_unique<AstNumberConstant>(1), std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX))));
    
    const RecursiveClauses& recursiveClauses = *translationUnit.getAnalysis<RecursiveClauses>();

    // first is the iteration number, which is counted inside each SCC
    if (recursiveClauses.recursive(&clause)) {
        positiveGenerationClause->getHead()->addArgument(std::make_unique<AstIterationNumber>());
    } else {
        positiveGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
    }

    // second is the previous epoch's count, which we set to 1, signifying that this tuple should have always existed, but was not generated in a prior epoch for some other reason
    // positiveGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));

    // third is the current epoch's count, which we set to 1, inserting a new tuple with positive count
    // THE CONSTANT 2 IS A HACK!!:
    // this will be detected in the AstTranslator and an appropriate re-insertion rule will be generated
    positiveGenerationClause->getHead()->addArgument(std::make_unique<AstNumberConstant>(2));

    // add constraint to the rule saying that all body atoms must have positive count
    positiveGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));

    /*
    // add constraint to the rule saying that all body atoms must have previously existed
    positiveGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                std::unique_ptr<AstArgument>(applyFunctorToVars(bodyPreviousCounts, FunctorOp::MIN)),
                std::make_unique<AstNumberConstant>(0)));
                */

    /*
    if (bodyLevels.size() > 0) {
        // add constraint to the rule saying that at least one body atom must have generated in the previous iteration
        positiveGenerationClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(applyFunctorToVars(bodyLevels, FunctorOp::MAX)),
                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
    }
    */

    return std::unique_ptr<AstClause>(positiveGenerationClause);
}

bool IncrementalTransformer::transform(AstTranslationUnit& translationUnit) {
    auto program = translationUnit.getProgram();

    std::cout << "before:\n";
    program->print(std::cout);
    std::cout << std::endl;

    for (auto relation : program->getRelations()) {
        // generate info relations for each clause
        // do this before all other transformations so that we record
        // the original rule without any instrumentation
        size_t clauseNum = 1;
        for (auto clause : relation->getClauses()) {
            if (!clause->isFact()) {
                clause->setClauseNum(clauseNum);

                // add info relation
                program->addRelation(makeProvInfoRelation(*clause, translationUnit));

                clauseNum++;
            }
        }
    }

    std::vector<AstRelation*> auxiliaryRelations;
    auto originalRelations = program->getRelations();

    // go through each relation and its rules to add annotations
    for (auto relation : program->getRelations()) {
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@iteration"), AstTypeIdentifier("number")));
        // relation->addAttribute(
        //         std::make_unique<AstAttribute>(std::string("@prev_count"), AstTypeIdentifier("number")));
        relation->addAttribute(
                std::make_unique<AstAttribute>(std::string("@current_count"), AstTypeIdentifier("number")));
    }

    for (auto relation : originalRelations) {
        // store a list of original clauses in the relation, to be deleted
        std::vector<AstClause*> originalClauses;

        for (auto clause : relation->getClauses()) {
            // mapper to add two provenance columns to atoms
            // add unnamed vars to each atom nested in arguments of head
            clause->getHead()->apply(addUnnamedVariables());

            // if fact, level number is 0
            if (clause->isFact()) {
                clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
                // clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(0));
                clause->getHead()->addArgument(std::make_unique<AstNumberConstant>(1));
            } else {
                for (auto clause : makeNegativeUpdateClause(*clause, translationUnit)) {
                    program->appendClause(std::unique_ptr<AstClause>(clause));
                }
                for (auto clause : makePositiveUpdateClause(*clause, translationUnit)) {
                    program->appendClause(std::unique_ptr<AstClause>(clause));
                }
                relation->addClause(std::unique_ptr<AstClause>(makeNegativeGenerationClause(*clause, translationUnit)));
                relation->addClause(std::unique_ptr<AstClause>(makePositiveGenerationClause(*clause, translationUnit)));

                originalClauses.push_back(clause);
            }
        }

        // delete original clauses once instrumented clauses are added
        for (auto clause : originalClauses) {
            relation->removeClause(clause);
        }
    }


    std::cout << "after:\n";
    program->print(std::cout);
    std::cout << std::endl;
    return true;
}

}  // end of namespace souffle
