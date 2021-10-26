/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file AstTranslator.cpp
 *
 * Translator from AST to RAM structures.
 *
 ***********************************************************************/

#include "AstTranslator.h"
#include "AstTransforms.h"
#include "AstArgument.h"
#include "AstAttribute.h"
#include "AstClause.h"
#include "AstFunctorDeclaration.h"
#include "AstIO.h"
#include "AstLiteral.h"
#include "AstNode.h"
#include "AstProgram.h"
#include "AstRelation.h"
#include "AstTranslationUnit.h"
#include "AstTypeEnvironmentAnalysis.h"
#include "AstUtils.h"
#include "AstVisitor.h"
#include "BinaryConstraintOps.h"
#include "DebugReport.h"
#include "Global.h"
#include "IODirectives.h"
#include "LogStatement.h"
#include "PrecedenceGraph.h"
#include "RamCondition.h"
#include "RamExpression.h"
#include "RamNode.h"
#include "RamOperation.h"
#include "RamProgram.h"
#include "RamRelation.h"
#include "RamStatement.h"
#include "RamTranslationUnit.h"
#include "SrcLocation.h"
#include "TypeSystem.h"
#include "Util.h"
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstddef>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <typeinfo>
#include <utility>
#include <vector>

namespace souffle {

class ErrorReport;
class SymbolTable;

std::unique_ptr<RamTupleElement> AstTranslator::makeRamTupleElement(const Location& loc) {
    return std::make_unique<RamTupleElement>(loc.identifier, loc.element);
}

void AstTranslator::makeIODirective(IODirectives& ioDirective, const AstRelation* rel,
        const std::string& filePath, const std::string& fileExt, const bool isIntermediate) {
    // set relation name correctly
    ioDirective.setRelationName(getRelationName(rel->getName()));

    // set a default IO type of file and a default filename if not supplied
    if (!ioDirective.has("IO")) {
        ioDirective.setIOType("file");
    }

    // load intermediate relations from correct files
    if (ioDirective.getIOType() == "file") {
        // all intermediate relations are given the default delimiter and have no headers
        if (isIntermediate) {
            ioDirective.set("intermediate", "true");
            ioDirective.set("delimiter", "\t");
            ioDirective.set("headers", "false");
        }

        // set filename by relation if not given, or if relation is intermediate
        if (!ioDirective.has("filename") || isIntermediate) {
            ioDirective.setFileName(ioDirective.getRelationName() + fileExt);
        }

        // if filename is not an absolute path, concat with cmd line facts directory
        if (ioDirective.getIOType() == "file" && ioDirective.getFileName().front() != '/') {
            ioDirective.setFileName(filePath + "/" + ioDirective.getFileName());
        }
    }
}

std::vector<IODirectives> AstTranslator::getInputIODirectives(
        const AstRelation* rel, std::string filePath, const std::string& fileExt) {
    std::vector<IODirectives> inputDirectives;

    for (const auto& current : rel->getLoads()) {
        IODirectives ioDirectives;
        for (const auto& currentPair : current->getIODirectiveMap()) {
            ioDirectives.set(currentPair.first, currentPair.second);
        }
        inputDirectives.push_back(ioDirectives);
    }

    if (inputDirectives.empty()) {
        inputDirectives.emplace_back();
    }

    const std::string inputFilePath = (filePath.empty()) ? Global::config().get("fact-dir") : filePath;
    const std::string inputFileExt = (fileExt.empty()) ? ".facts" : fileExt;

    const bool isIntermediate =
            (Global::config().has("engine") && inputFilePath == Global::config().get("output-dir") &&
                    inputFileExt == ".facts");

    for (auto& ioDirective : inputDirectives) {
        makeIODirective(ioDirective, rel, inputFilePath, inputFileExt, isIntermediate);
    }

    return inputDirectives;
}

std::vector<IODirectives> AstTranslator::getOutputIODirectives(
        const AstRelation* rel, std::string filePath, const std::string& fileExt) {
    std::vector<IODirectives> outputDirectives;

    // If stdout is requested then remove all directives from the datalog file.
    if (Global::config().get("output-dir") == "-") {
        bool hasOutput = false;
        for (const auto* current : rel->getStores()) {
            IODirectives ioDirectives;
            if (dynamic_cast<const AstPrintSize*>(current) != nullptr) {
                ioDirectives.setIOType("stdoutprintsize");
                outputDirectives.push_back(ioDirectives);
            } else if (!hasOutput) {
                hasOutput = true;
                ioDirectives.setIOType("stdout");
                ioDirectives.set("headers", "true");
                outputDirectives.push_back(ioDirectives);
            }
        }
    } else {
        for (const auto* current : rel->getStores()) {
            IODirectives ioDirectives;
            for (const auto& currentPair : current->getIODirectiveMap()) {
                ioDirectives.set(currentPair.first, currentPair.second);
            }
            outputDirectives.push_back(ioDirectives);
        }
    }

    if (outputDirectives.empty()) {
        outputDirectives.emplace_back();
    }

    const std::string outputFilePath = (filePath.empty()) ? Global::config().get("output-dir") : filePath;
    const std::string outputFileExt = (fileExt.empty()) ? ".csv" : fileExt;

    const bool isIntermediate =
            (Global::config().has("engine") && outputFilePath == Global::config().get("output-dir") &&
                    outputFileExt == ".facts");

    for (auto& ioDirective : outputDirectives) {
        makeIODirective(ioDirective, rel, outputFilePath, outputFileExt, isIntermediate);

        if (!ioDirective.has("attributeNames")) {
            std::string delimiter("\t");
            if (ioDirective.has("delimiter")) {
                delimiter = ioDirective.get("delimiter");
            }
            std::vector<std::string> attributeNames;
            for (unsigned int i = 0; i < rel->getArity(); i++) {
                attributeNames.push_back(rel->getAttribute(i)->getAttributeName());
            }

            if (Global::config().has("provenance")) {
                std::vector<std::string> originalAttributeNames(
                        attributeNames.begin(), attributeNames.end() - 1 - rel->numberOfHeightParameters());
                ioDirective.set("attributeNames", toString(join(originalAttributeNames, delimiter)));
            } else {
                ioDirective.set("attributeNames", toString(join(attributeNames, delimiter)));
            }
        }
    }

    return outputDirectives;
}

std::unique_ptr<RamRelationReference> AstTranslator::createRelationReference(const std::string name,
        const size_t arity, const size_t numberOfHeights, const std::vector<std::string> attributeNames,
        const std::vector<std::string> attributeTypeQualifiers, const RelationRepresentation representation) {
    const RamRelation* ramRel = ramProg->getRelation(name);
    if (ramRel == nullptr) {
        ramProg->addRelation(std::make_unique<RamRelation>(
                name, arity, numberOfHeights, attributeNames, attributeTypeQualifiers, representation));
        ramRel = ramProg->getRelation(name);
        assert(ramRel != nullptr && "cannot find relation");
    }
    return std::make_unique<RamRelationReference>(ramRel);
}

std::unique_ptr<RamRelationReference> AstTranslator::createRelationReference(
        const std::string name, const size_t arity, const size_t numberOfHeights) {
    return createRelationReference(name, arity, numberOfHeights, {}, {}, {});
}

std::unique_ptr<RamRelationReference> AstTranslator::translateRelation(const AstAtom* atom) {
    if (const auto rel = getAtomRelation(atom, program)) {
        return translateRelation(rel);
    } else {
        return createRelationReference(
                getRelationName(atom->getName()), atom->getArity(), getNumberOfHeights(atom, program));
    }
}

std::unique_ptr<RamRelationReference> AstTranslator::translateRelation(
        const AstRelation* rel, const std::string relationNamePrefix) {
    std::vector<std::string> attributeNames;
    std::vector<std::string> attributeTypeQualifiers;
    for (size_t i = 0; i < rel->getArity(); ++i) {
        attributeNames.push_back(rel->getAttribute(i)->getAttributeName());
        if (typeEnv) {
            attributeTypeQualifiers.push_back(
                    getTypeQualifier(typeEnv->getType(rel->getAttribute(i)->getTypeName())));
        }
    }

    return createRelationReference(relationNamePrefix + getRelationName(rel->getName()), rel->getArity(),
            rel->numberOfHeightParameters(), attributeNames, attributeTypeQualifiers,
            rel->getRepresentation());
}

std::unique_ptr<RamRelationReference> AstTranslator::translateDeltaRelation(const AstRelation* rel) {
    return translateRelation(rel, "@delta_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateNewRelation(const AstRelation* rel) {
    return translateRelation(rel, "@new_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateDiffMinusRelation(
        const AstRelation* rel) {
    return translateRelation(rel, "diff_minus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateDiffPlusRelation(
        const AstRelation* rel) {
    return translateRelation(rel, "diff_plus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateUpdatedMinusRelation(
        const AstRelation* rel) {
    return translateRelation(rel, "updated_minus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateUpdatedPlusRelation(
        const AstRelation* rel) {
    return translateRelation(rel, "updated_plus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateNewDiffAppliedRelation(const AstRelation* rel) {
    return translateRelation(rel, "@new_diff_applied@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateNewDiffMinusRelation(const AstRelation* rel) {
    return translateRelation(rel, "@new_diff_minus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateNewDiffPlusRelation(const AstRelation* rel) {
    return translateRelation(rel, "@new_diff_plus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateDeltaDiffAppliedRelation(const AstRelation* rel) {
    return translateRelation(rel, "@delta_diff_applied@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateActualDiffMinusRelation(const AstRelation* rel) {
    return translateRelation(rel, "actual_diff_minus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateActualDiffPlusRelation(const AstRelation* rel) {
    return translateRelation(rel, "actual_diff_plus@_");
}

std::unique_ptr<RamRelationReference> AstTranslator::translateDiffAppliedRelation(
        const AstRelation* rel) {
    return translateRelation(rel, "diff_applied@_");
}

std::unique_ptr<RamExpression> AstTranslator::translateValue(
        const AstArgument* arg, const ValueIndex& index) {
    if (arg == nullptr) {
        return nullptr;
    }

    class ValueTranslator : public AstVisitor<std::unique_ptr<RamExpression>> {
        AstTranslator& translator;
        const ValueIndex& index;

    public:
        ValueTranslator(AstTranslator& translator, const ValueIndex& index)
                : translator(translator), index(index) {}

        std::unique_ptr<RamExpression> visitVariable(const AstVariable& var) override {
            assert(index.isDefined(var) && "variable not grounded");
            return makeRamTupleElement(index.getDefinitionPoint(var));
        }

        std::unique_ptr<RamExpression> visitUnnamedVariable(const AstUnnamedVariable& var) override {
            return std::make_unique<RamUndefValue>();
        }

        std::unique_ptr<RamExpression> visitConstant(const AstConstant& c) override {
            return std::make_unique<RamNumber>(c.getIndex());
        }

        std::unique_ptr<RamExpression> visitIntrinsicFunctor(const AstIntrinsicFunctor& inf) override {
            std::vector<std::unique_ptr<RamExpression>> values;
            for (const auto& cur : inf.getArguments()) {
                values.push_back(translator.translateValue(cur, index));
            }
            return std::make_unique<RamIntrinsicOperator>(inf.getFunction(), std::move(values));
        }

        std::unique_ptr<RamExpression> visitUserDefinedFunctor(const AstUserDefinedFunctor& udf) override {
            std::vector<std::unique_ptr<RamExpression>> values;
            for (const auto& cur : udf.getArguments()) {
                values.push_back(translator.translateValue(cur, index));
            }
            const AstFunctorDeclaration* decl = translator.program->getFunctorDeclaration(udf.getName());
            std::string type = decl->getType();
            return std::make_unique<RamUserDefinedOperator>(udf.getName(), type, std::move(values));
        }

        std::unique_ptr<RamExpression> visitCounter(const AstCounter&) override {
            return std::make_unique<RamAutoIncrement>();
        }

        std::unique_ptr<RamExpression> visitIterationNumber(const AstIterationNumber&) override {
            return std::make_unique<RamIterationNumber>();
        }

        std::unique_ptr<RamExpression> visitRecordInit(const AstRecordInit& init) override {
            std::vector<std::unique_ptr<RamExpression>> values;
            for (const auto& cur : init.getArguments()) {
                values.push_back(translator.translateValue(cur, index));
            }
            return std::make_unique<RamPackRecord>(std::move(values));
        }

        std::unique_ptr<RamExpression> visitAggregator(const AstAggregator& agg) override {
            // here we look up the location the aggregation result gets bound
            return translator.makeRamTupleElement(index.getAggregatorLocation(agg));
        }

        std::unique_ptr<RamExpression> visitSubroutineArgument(const AstSubroutineArgument& subArg) override {
            return std::make_unique<RamSubroutineArgument>(subArg.getNumber());
        }
    };

    return ValueTranslator(*this, index)(*arg);
}

std::unique_ptr<RamCondition> AstTranslator::translateConstraint(
        const AstLiteral* lit, const ValueIndex& index) {
    class ConstraintTranslator : public AstVisitor<std::unique_ptr<RamCondition>> {
        AstTranslator& translator;
        const ValueIndex& index;

    public:
        ConstraintTranslator(AstTranslator& translator, const ValueIndex& index)
                : translator(translator), index(index) {}

        /** for atoms */
        std::unique_ptr<RamCondition> visitAtom(const AstAtom&) override {
            return nullptr;  // covered already within the scan/lookup generation step
        }

        /** for binary relations */
        std::unique_ptr<RamCondition> visitBinaryConstraint(const AstBinaryConstraint& binRel) override {
            std::unique_ptr<RamExpression> valLHS = translator.translateValue(binRel.getLHS(), index);
            std::unique_ptr<RamExpression> valRHS = translator.translateValue(binRel.getRHS(), index);
            return std::make_unique<RamConstraint>(binRel.getOperator(),
                    translator.translateValue(binRel.getLHS(), index),
                    translator.translateValue(binRel.getRHS(), index));
        }

        /** for conjunctions */
        std::unique_ptr<RamCondition> visitConjunctionConstraint(const AstConjunctionConstraint& conjunctionConstraint) override {
            std::unique_ptr<RamCondition> valLHS = translator.translateConstraint(conjunctionConstraint.getLHS(), index);
            std::unique_ptr<RamCondition> valRHS = translator.translateConstraint(conjunctionConstraint.getRHS(), index);
            return std::make_unique<RamConjunction>(std::move(valLHS), std::move(valRHS));
        }

        /** for disjunctions */
        std::unique_ptr<RamCondition> visitDisjunctionConstraint(const AstDisjunctionConstraint& disjunctionConstraint) override {
            std::unique_ptr<RamCondition> valLHS = translator.translateConstraint(disjunctionConstraint.getLHS(), index);
            std::unique_ptr<RamCondition> valRHS = translator.translateConstraint(disjunctionConstraint.getRHS(), index);
            return std::make_unique<RamDisjunction>(std::move(valLHS), std::move(valRHS));
        }

        /** for provenance negation */
        std::unique_ptr<RamCondition> visitExistenceCheck(const AstExistenceCheck& exists) override {
            // get contained atom
            const AstAtom* atom = exists.getAtom();
            auto arity = atom->getArity();

            std::vector<std::unique_ptr<RamExpression>> values;

            for (size_t i = 0; i < arity; i++) {
                const auto& arg = atom->getArgument(i);
                values.push_back(translator.translateValue(arg, index));
            }

            // add constraint
            return std::make_unique<RamPositiveExistenceCheck>(
                    translator.translateRelation(atom), std::move(values));
        }

        /** for negations */
        std::unique_ptr<RamCondition> visitNegation(const AstNegation& neg) override {
            // get contained atom
            const auto* atom = neg.getAtom();
            auto arity = atom->getArity();
            auto numberOfHeightParameters = getNumberOfHeights(atom, translator.program);

            // account for extra provenance columns
            if (Global::config().has("provenance")) {
                // rule number
                arity -= 1;
                // height parameters
                arity -= numberOfHeightParameters;
            }

            std::vector<std::unique_ptr<RamExpression>> values;

            for (size_t i = 0; i < arity; i++) {
                values.push_back(translator.translateValue(atom->getArgument(i), index));
            }

            // we don't care about the provenance columns when doing the existence check
            if (Global::config().has("provenance")) {
                values.push_back(std::make_unique<RamUndefValue>());
                for (size_t h = 0; h < numberOfHeightParameters; h++) {
                    values.push_back(std::make_unique<RamUndefValue>());
                }
            }

            // add constraint
            if (arity > 0) {
                return std::make_unique<RamNegation>(std::make_unique<RamExistenceCheck>(
                        translator.translateRelation(atom), std::move(values)));
            } else {
                return std::make_unique<RamEmptinessCheck>(translator.translateRelation(atom));
            }
        }

        /** for provenance negation */
        std::unique_ptr<RamCondition> visitPositiveNegation(const AstPositiveNegation& neg) override {
            // get contained atom
            const AstAtom* atom = neg.getAtom();
            auto arity = atom->getArity();

            std::vector<std::unique_ptr<RamExpression>> values;

            for (size_t i = 0; i < arity; i++) {
                const auto& arg = atom->getArgument(i);
                values.push_back(translator.translateValue(arg, index));
            }

            // add constraint
            return std::make_unique<RamNegation>(std::make_unique<RamPositiveExistenceCheck>(
                    translator.translateRelation(atom), std::move(values)));
        }

        /** for provenance negation */
        std::unique_ptr<RamCondition> visitSubsumptionNegation(const AstSubsumptionNegation& neg) override {
            // get contained atom
            const AstAtom* atom = neg.getAtom();
            auto arity = atom->getArity();
            auto subsumptionArity = arity - neg.getNumSubsumptionFields();

            /*
            auto numberOfHeightParameters = getNumberOfHeights(atom, translator.program);

            // account for extra provenance columns
            if (Global::config().has("provenance")) {
                // rule number
                arity -= 1;
                // level numbers
                arity -= numberOfHeightParameters;
            }
            */

            std::vector<std::unique_ptr<RamExpression>> values;

            // for (size_t i = 0; i < subsumptionArity; i++) {
            for (size_t i = 0; i < arity; i++) {
                const auto& arg = atom->getArgument(i);
                // for (const auto& arg : atom->getArguments()) {
                values.push_back(translator.translateValue(arg, index));
            }

            /*
            // we don't care about the provenance columns when doing the existence check
            if (Global::config().has("provenance")) {
                values.push_back(std::make_unique<RamUndefValue>());
                // add the height annotation for provenanceNotExists
                for (size_t h = 0; h < numberOfHeightParameters; h++)
                    values.push_back(translator.translateValue(atom->getArgument(arity + h + 1), index));
            }
            */

            // add constraint
            return std::make_unique<RamNegation>(std::make_unique<RamSubsumptionExistenceCheck>(
                    translator.translateRelation(atom), std::move(values)));
        }
    };

    return ConstraintTranslator(*this, index)(*lit);
}

std::unique_ptr<AstClause> AstTranslator::ClauseTranslator::getReorderedClause(
        const AstClause& clause, const int version, const int version2) const {
    const auto plan = clause.getExecutionPlan();

    // check whether there is an imposed order constraint
    if (plan != nullptr && plan->hasOrderFor(version, version2)) {
        // get the imposed order
        const auto& order = plan->getOrderFor(version, version2);

        // create a copy and fix order
        std::unique_ptr<AstClause> reorderedClause(clause.clone());

        if (Global::config().has("incremental")) {
            // these should not be nullptrs
            // auto prevCountNum = dynamic_cast<AstNumberConstant*>(clause.getHead()->getArgument(clause.getHead()->getArity() - 2));
            auto curCountNum = dynamic_cast<AstNumberConstant*>(clause.getHead()->getArgument(clause.getHead()->getArity() - 1));

            // check if this clause is re-inserting hidden tuples
            // bool isReinsertionRule = (*prevCountNum == AstNumberConstant(1) && *curCountNum == AstNumberConstant(2));
            // a re-insertion rule has one extra atom which checks the diff_minus version of the relation
            bool isReinsertionRule = clause.getAtoms().size() == order.size() + 1;

            if (isReinsertionRule) {
                // Change order to start at zero
                std::vector<unsigned int> newOrder(order.size() + 1);

                std::transform(order.begin(), order.end(), newOrder.begin() + 1,
                        [](unsigned int i) -> unsigned int { return i; });

                // re-order atoms
                reorderedClause->reorderAtoms(newOrder);
            } else {
                // Change order to start at zero
                std::vector<unsigned int> newOrder(order.size());
                std::transform(order.begin(), order.end(), newOrder.begin(),
                        [](unsigned int i) -> unsigned int { return i - 1; });

                // re-order atoms
                reorderedClause->reorderAtoms(newOrder);
            }
        } else {
            // Change order to start at zero
            std::vector<unsigned int> newOrder(order.size());
            std::transform(order.begin(), order.end(), newOrder.begin(),
                    [](unsigned int i) -> unsigned int { return i - 1; });

            // re-order atoms
            reorderedClause->reorderAtoms(newOrder);
        }

        // clear other order and fix plan
        reorderedClause->clearExecutionPlan();
        reorderedClause->setFixedExecutionPlan();

        return reorderedClause;
    }

    return nullptr;
}

AstTranslator::ClauseTranslator::arg_list* AstTranslator::ClauseTranslator::getArgList(
        const AstNode* curNode, std::map<const AstNode*, std::unique_ptr<arg_list>>& nodeArgs) const {
    if (!nodeArgs.count(curNode)) {
        if (auto rec = dynamic_cast<const AstRecordInit*>(curNode)) {
            nodeArgs[curNode] = std::make_unique<arg_list>(rec->getArguments());
        } else if (auto atom = dynamic_cast<const AstAtom*>(curNode)) {
            nodeArgs[curNode] = std::make_unique<arg_list>(atom->getArguments());
        } else {
            assert(false && "node type doesn't have arguments!");
        }
    }
    return nodeArgs[curNode].get();
}

void AstTranslator::ClauseTranslator::indexValues(const AstNode* curNode,
        std::map<const AstNode*, std::unique_ptr<arg_list>>& nodeArgs,
        std::map<const arg_list*, int>& arg_level, RamRelationReference* relation) {
    arg_list* cur = getArgList(curNode, nodeArgs);
    for (size_t pos = 0; pos < cur->size(); ++pos) {
        // get argument
        auto& arg = (*cur)[pos];

        // check for variable references
        if (auto var = dynamic_cast<const AstVariable*>(arg)) {
            if (pos < relation->get()->getArity()) {
                valueIndex.addVarReference(
                        *var, arg_level[cur], pos, std::unique_ptr<RamRelationReference>(relation->clone()));
            } else {
                valueIndex.addVarReference(*var, arg_level[cur], pos);
            }
        }

        // check for nested records
        if (auto rec = dynamic_cast<const AstRecordInit*>(arg)) {
            // introduce new nesting level for unpack
            op_nesting.push_back(rec);
            arg_level[getArgList(rec, nodeArgs)] = level++;

            // register location of record
            valueIndex.setRecordDefinition(*rec, arg_level[cur], pos);

            // resolve nested components
            indexValues(rec, nodeArgs, arg_level, relation);
        }
    }
}

/** index values in rule */
void AstTranslator::ClauseTranslator::createValueIndex(const AstClause& clause) {
    for (const AstAtom* atom : clause.getAtoms()) {
        // std::map<const arg_list*, int> arg_level;
        std::map<const AstNode*, std::unique_ptr<arg_list>> nodeArgs;

        std::map<const arg_list*, int> arg_level;
        nodeArgs[atom] = std::make_unique<arg_list>(atom->getArguments());
        // the atom is obtained at the current level
        // increment nesting level for the atom
        arg_level[nodeArgs[atom].get()] = level++;
        op_nesting.push_back(atom);

        indexValues(atom, nodeArgs, arg_level, translator.translateRelation(atom).get());
    }

    // add aggregation functions
    visitDepthFirstPostOrder(clause, [&](const AstAggregator& cur) {
        // add each aggregator expression only once
        if (any_of(aggregators, [&](const AstAggregator* agg) { return *agg == cur; })) {
            return;
        }

        int aggLoc = level++;
        valueIndex.setAggregatorLocation(cur, Location({aggLoc, 0}));

        // bind aggregator variables to locations
        assert(nullptr != dynamic_cast<const AstAtom*>(cur.getBodyLiterals()[0]));
        const AstAtom& atom = static_cast<const AstAtom&>(*cur.getBodyLiterals()[0]);
        for (size_t pos = 0; pos < atom.getArguments().size(); ++pos) {
            if (const auto* var = dynamic_cast<const AstVariable*>(atom.getArgument(pos))) {
                valueIndex.addVarReference(*var, aggLoc, (int)pos, translator.translateRelation(&atom));
            }
        };

        // and remember aggregator
        aggregators.push_back(&cur);
    });
}

std::unique_ptr<RamOperation> AstTranslator::ClauseTranslator::createOperation(const AstClause& clause) {
    const auto head = clause.getHead();

    std::vector<std::unique_ptr<RamExpression>> values;
    for (AstArgument* arg : head->getArguments()) {
        values.push_back(translator.translateValue(arg, valueIndex));
    }

    std::unique_ptr<RamOperation> project =
            std::make_unique<RamProject>(translator.translateRelation(head), std::move(values));

    if (head->getArity() == 0) {
        project = std::make_unique<RamFilter>(
                std::make_unique<RamEmptinessCheck>(translator.translateRelation(head)), std::move(project));
    }

    // check existence for original tuple if we have provenance
    // only if we don't compile
    if (Global::config().has("provenance") &&
            ((!Global::config().has("compile") && !Global::config().has("dl-program") &&
                    !Global::config().has("generate")))) {
        size_t numberOfHeights = getNumberOfHeights(head, translator.program);

        auto arity = head->getArity() - 1 - numberOfHeights;

        std::vector<std::unique_ptr<RamExpression>> values;

        bool isVolatile = true;
        // add args for original tuple
        for (size_t i = 0; i < arity; i++) {
            auto arg = head->getArgument(i);

            // don't add counters
            visitDepthFirst(*arg, [&](const AstCounter& cur) { isVolatile = false; });
            values.push_back(translator.translateValue(arg, valueIndex));
        }

        // add unnamed args for provenance columns
        values.push_back(std::make_unique<RamUndefValue>());
        for (size_t h = 0; h < numberOfHeights; h++) {
            values.push_back(std::make_unique<RamUndefValue>());
        }

        if (isVolatile) {
            return std::make_unique<RamFilter>(
                    std::make_unique<RamNegation>(std::make_unique<RamExistenceCheck>(
                            translator.translateRelation(head), std::move(values))),
                    std::move(project));
        }
    }

    // build up insertion call
    return project;  // start with innermost
}

std::unique_ptr<RamOperation> AstTranslator::ProvenanceClauseTranslator::createOperation(
        const AstClause& clause) {
    std::vector<std::unique_ptr<RamExpression>> values;

    // set a rule number that is used to display the current clause
    values.push_back(std::make_unique<RamNumber>(clause.getClauseNum()));

    // keep a set of count arguments
    std::set<AstArgument*> countArgs;
    for (AstLiteral* lit : clause.getBodyLiterals()) {
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            countArgs.insert(atom->getArgument(atom->getArity() - 1)->clone());
        }
    }

    // get all values in the body
    for (AstLiteral* lit : clause.getBodyLiterals()) {
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            for (AstArgument* arg : atom->getArguments()) {
                values.push_back(translator.translateValue(arg, valueIndex));
            }
        } else if (auto neg = dynamic_cast<AstNegation*>(lit)) {
            for (AstArgument* arg : neg->getAtom()->getArguments()) {
                values.push_back(translator.translateValue(arg, valueIndex));
            }
        } else if (auto con = dynamic_cast<AstBinaryConstraint*>(lit)) {
            // ignore any constraints involving count annotation or any subroutine arguments
            if (dynamic_cast<AstSubroutineArgument*>(con->getLHS()) || dynamic_cast<AstSubroutineArgument*>(con->getRHS())) {
                continue;
            }

            bool isCountArg = false;
            for (auto arg : countArgs) {
                if (*(con->getLHS()) == *arg || *(con->getRHS()) == *arg) {
                    isCountArg = true;
                    break;
                }
            }

            if (isCountArg) continue;

            values.push_back(translator.translateValue(con->getLHS(), valueIndex));
            values.push_back(translator.translateValue(con->getRHS(), valueIndex));
        } else if (auto neg = dynamic_cast<AstSubsumptionNegation*>(lit)) {
            size_t numberOfHeights = getNumberOfHeights(neg->getAtom(), translator.program);

            // non provenance arguments
            for (size_t i = 0; i < neg->getAtom()->getArguments().size() - 1 - numberOfHeights; ++i) {
                auto arg = neg->getAtom()->getArguments()[i];
                values.push_back(translator.translateValue(arg, valueIndex));
            }

            // provenance annotation arguments
            for (size_t i = 0; i < numberOfHeights + 1; ++i)
                values.push_back(std::make_unique<RamNumber>(-1));
        }
    }

    return std::make_unique<RamSubroutineReturnValue>(std::move(values));
}

std::unique_ptr<RamCondition> AstTranslator::ClauseTranslator::createCondition(
        const AstClause& originalClause) {
    const auto head = originalClause.getHead();

    // add stopping criteria for nullary relations
    // (if it contains already the null tuple, don't re-compute)
    if (head->getArity() == 0) {
        return std::make_unique<RamEmptinessCheck>(translator.translateRelation(head));
    }
    return nullptr;
}

std::unique_ptr<RamCondition> AstTranslator::ProvenanceClauseTranslator::createCondition(
        const AstClause& originalClause) {
    return nullptr;
}

/** generate RAM code for a clause */
std::unique_ptr<RamStatement> AstTranslator::ClauseTranslator::translateClause(
        const AstClause& oldClause, const AstClause& originalClause, const int version, const int version2) {
    if (auto reorderedClause = getReorderedClause(oldClause, version, version2)) {
        // translate reordered clause
        return translateClause(*reorderedClause, originalClause, version, version2);
    }

    // get extract some details
    const AstAtom* head = oldClause.getHead();

    // handle facts
    if (oldClause.isFact()) {
        // translate arguments
        std::vector<std::unique_ptr<RamExpression>> values;
        for (auto& arg : head->getArguments()) {
            values.push_back(translator.translateValue(arg, ValueIndex()));
        }

        // create a fact statement
        return std::make_unique<RamFact>(translator.translateRelation(head), std::move(values));
    }

    // the rest should be rules
    assert(oldClause.isRule());

    // re-run ResolveAliasesTransformer, as some modifications to rules have occurred in the AstTranslator,
    // meaning that functors could exist without being properly grounded
    auto clausePtr = ResolveAliasesTransformer::removeComplexTermsInAtoms(oldClause);
    const AstClause& clause = *clausePtr;

    createValueIndex(clause);

    // -- create RAM statement --

    std::unique_ptr<RamOperation> op = createOperation(clause);

    /* add equivalence constraints imposed by variable binding */
    for (const auto& cur : valueIndex.getVariableReferences()) {
        // the first appearance
        const Location& first = *cur.second.begin();
        // all other appearances
        for (const Location& loc : cur.second) {
            if (first != loc && !valueIndex.isAggregator(loc.identifier)) {
                op = std::make_unique<RamFilter>(
                        std::make_unique<RamConstraint>(
                                BinaryConstraintOp::EQ, makeRamTupleElement(first), makeRamTupleElement(loc)),
                        std::move(op));
            }
        }
    }

    /* add conditions caused by atoms, negations, and binary relations */
    for (const auto& lit : clause.getBodyLiterals()) {
        if (auto condition = translator.translateConstraint(lit, valueIndex)) {
            op = std::make_unique<RamFilter>(std::move(condition), std::move(op));
        }
    }

    // add aggregator conditions
    size_t curLevel = op_nesting.size() - 1;
    for (auto it = op_nesting.rbegin(); it != op_nesting.rend(); ++it, --curLevel) {
        const AstNode* cur = *it;

        if (const auto* atom = dynamic_cast<const AstAtom*>(cur)) {
            // add constraints
            for (size_t pos = 0; pos < atom->argSize(); ++pos) {
                if (auto* agg = dynamic_cast<AstAggregator*>(atom->getArgument(pos))) {
                    auto loc = valueIndex.getAggregatorLocation(*agg);
                    op = std::make_unique<RamFilter>(std::make_unique<RamConstraint>(BinaryConstraintOp::EQ,
                                                             std::make_unique<RamTupleElement>(curLevel, pos),
                                                             makeRamTupleElement(loc)),
                            std::move(op));
                }
            }
        }
    }

    // add aggregator levels
    --level;
    for (auto it = aggregators.rbegin(); it != aggregators.rend(); ++it, --level) {
        const AstAggregator* cur = *it;

        // translate aggregation function
        AggregateFunction fun = souffle::MIN;
        switch (cur->getOperator()) {
            case AstAggregator::min:
                fun = souffle::MIN;
                break;
            case AstAggregator::max:
                fun = souffle::MAX;
                break;
            case AstAggregator::count:
                fun = souffle::COUNT;
                break;
            case AstAggregator::sum:
                fun = souffle::SUM;
                break;
        }

        // condition for aggregate and helper function to add terms
        std::unique_ptr<RamCondition> aggCondition;
        auto addAggCondition = [&](std::unique_ptr<RamCondition>& arg) {
            if (aggCondition == nullptr) {
                aggCondition = std::move(arg);
            } else {
                aggCondition = std::make_unique<RamConjunction>(std::move(aggCondition), std::move(arg));
            }
        };

        // translate constraints of sub-clause
        for (const auto& lit : cur->getBodyLiterals()) {
            if (auto newCondition = translator.translateConstraint(lit, valueIndex)) {
                addAggCondition(newCondition);
            }
        }

        // get the first predicate of the sub-clause
        // NB: at most one atom is permitted in a sub-clause
        const AstAtom* atom = nullptr;
        for (const auto& lit : cur->getBodyLiterals()) {
            if (atom == nullptr) {
                atom = dynamic_cast<const AstAtom*>(lit);
            } else {
                assert(dynamic_cast<const AstAtom*>(lit) != nullptr &&
                        "Unsupported complex aggregation body encountered!");
            }
        }

        // translate arguments's of atom (if exists) to conditions
        if (atom != nullptr) {
            for (size_t pos = 0; pos < atom->argSize(); ++pos) {
                // variable bindings are issued differently since we don't want self
                // referential variable bindings
                if (const auto* var = dynamic_cast<const AstVariable*>(atom->getArgument(pos))) {
                    for (const Location& loc :
                            valueIndex.getVariableReferences().find(var->getName())->second) {
                        if (level != loc.identifier || (int)pos != loc.element) {
                            std::unique_ptr<RamCondition> newCondition = std::make_unique<RamConstraint>(
                                    BinaryConstraintOp::EQ, makeRamTupleElement(loc),
                                    std::make_unique<RamTupleElement>(level, pos));
                            addAggCondition(newCondition);
                            break;
                        }
                    }
                } else if (atom->getArgument(pos) != nullptr) {
                    std::unique_ptr<RamExpression> value =
                            translator.translateValue(atom->getArgument(pos), valueIndex);
                    if (value != nullptr && !isRamUndefValue(value.get())) {
                        std::unique_ptr<RamCondition> newCondition =
                                std::make_unique<RamConstraint>(BinaryConstraintOp::EQ,
                                        std::make_unique<RamTupleElement>(level, pos), std::move(value));
                        addAggCondition(newCondition);
                    }
                }
            }
        }

        // translate aggregate expression
        std::unique_ptr<RamExpression> expr =
                translator.translateValue(cur->getTargetExpression(), valueIndex);
        if (expr == nullptr) {
            expr = std::make_unique<RamUndefValue>();
        }

        if (aggCondition == nullptr) {
            aggCondition = std::make_unique<RamTrue>();
        }

        // add Ram-Aggregation layer
        std::unique_ptr<RamAggregate> aggregate = std::make_unique<RamAggregate>(std::move(op), fun,
                translator.translateRelation(atom), std::move(expr), std::move(aggCondition), level);
        op = std::move(aggregate);
    }

    /*
    bool isInsertionRule = false;

    if (Global::config().has("incremental")) {
        // store previous count and current count to determine if the rule is insertion or deletion
        auto prevCount = clause.getHead()->getArgument(clause.getHead()->getArity() - 2);
        auto curCount = clause.getHead()->getArgument(clause.getHead()->getArity() - 1);

        // these should not be nullptrs
        auto prevCountNum = dynamic_cast<AstNumberConstant*>(prevCount);
        auto curCountNum = dynamic_cast<AstNumberConstant*>(curCount);

        isInsertionRule = (*curCountNum == AstNumberConstant(1)) && (*prevCountNum == AstNumberConstant(0));
    }
    */

    // build operation bottom-up
    while (!op_nesting.empty()) {
        // get next operator
        const AstNode* cur = op_nesting.back();
        op_nesting.pop_back();

        // get current nesting level
        auto level = op_nesting.size();

        if (const auto* atom = dynamic_cast<const AstAtom*>(cur)) {
            // add constraints
            for (size_t pos = 0; pos < atom->argSize(); ++pos) {
                if (auto* c = dynamic_cast<AstConstant*>(atom->getArgument(pos))) {
                    op = std::make_unique<RamFilter>(std::make_unique<RamConstraint>(BinaryConstraintOp::EQ,
                                                             std::make_unique<RamTupleElement>(level, pos),
                                                             std::make_unique<RamNumber>(c->getIndex())),
                            std::move(op));
                }
            }

            // check whether all arguments are unnamed variables
            bool isAllArgsUnnamed = true;
            for (auto* argument : atom->getArguments()) {
                if (dynamic_cast<AstUnnamedVariable*>(argument) == nullptr) {
                    isAllArgsUnnamed = false;
                }
            }

            // assume any added negation searches are at the end of the rule, so level < version2 - 1 should only hold for originally positive atoms in the body
            /*
            if (isInsertionRule && version2 > 1 && level < version2 - 1) {
                // add check for emptiness for the full version of the relation
                op = std::make_unique<RamFilter>(
                        std::make_unique<RamNegation>(
                                std::make_unique<RamEmptinessCheck>(translator.translateRelation(originalClause.getAtoms()[level]))),
                        std::move(op));
            }
            */

            // add check for emptiness for an atom
            op = std::make_unique<RamFilter>(
                    std::make_unique<RamNegation>(
                            std::make_unique<RamEmptinessCheck>(translator.translateRelation(atom))),
                    std::move(op));

            // add a scan level
            if (atom->getArity() != 0 && !isAllArgsUnnamed) {
                if (head->getArity() == 0) {
                    op = std::make_unique<RamBreak>(
                            std::make_unique<RamNegation>(
                                    std::make_unique<RamEmptinessCheck>(translator.translateRelation(head))),
                            std::move(op));
                }
                if (Global::config().has("profile")) {
                    std::stringstream ss;
                    ss << head->getName();
                    ss.str("");
                    ss << "@frequency-atom" << ';';
                    ss << originalClause.getHead()->getName() << ';';
                    ss << version << ';';
                    ss << stringify(toString(clause)) << ';';
                    ss << stringify(toString(*atom)) << ';';
                    ss << stringify(toString(originalClause)) << ';';
                    ss << level << ';';
                    op = std::make_unique<RamScan>(
                            translator.translateRelation(atom), level, std::move(op), ss.str());
                } else {
                    op = std::make_unique<RamScan>(translator.translateRelation(atom), level, std::move(op));
                }
            }

            // TODO: support constants in nested records!
        } else if (const auto* rec = dynamic_cast<const AstRecordInit*>(cur)) {
            // add constant constraints
            for (size_t pos = 0; pos < rec->getArguments().size(); ++pos) {
                if (AstConstant* c = dynamic_cast<AstConstant*>(rec->getArguments()[pos])) {
                    op = std::make_unique<RamFilter>(std::make_unique<RamConstraint>(BinaryConstraintOp::EQ,
                                                             std::make_unique<RamTupleElement>(level, pos),
                                                             std::make_unique<RamNumber>(c->getIndex())),
                            std::move(op));
                } else if (AstFunctor* func = dynamic_cast<AstFunctor*>(rec->getArguments()[pos])) {
                    op = std::make_unique<RamFilter>(std::make_unique<RamConstraint>(BinaryConstraintOp::EQ,
                                                             std::make_unique<RamTupleElement>(level, pos),
                                                             translator.translateValue(func, valueIndex)),
                            std::move(op));
                }
            }

            // add an unpack level
            const Location& loc = valueIndex.getDefinitionPoint(*rec);
            op = std::make_unique<RamUnpackRecord>(
                    std::move(op), level, makeRamTupleElement(loc), rec->getArguments().size());
        } else {
            assert(false && "Unsupported AST node for creation of scan-level!");
        }
    }

    /* generate the final RAM Insert statement */
    std::unique_ptr<RamCondition> cond = createCondition(originalClause);
    if (cond != nullptr) {
        return std::make_unique<RamQuery>(std::make_unique<RamFilter>(std::move(cond), std::move(op)));
    } else {
        return std::make_unique<RamQuery>(std::move(op));
    }
}

/* utility for appending statements */
void AstTranslator::appendStmt(std::unique_ptr<RamStatement>& stmtList, std::unique_ptr<RamStatement> stmt) {
    if (stmt) {
        if (stmtList) {
            RamSequence* stmtSeq;
            if ((stmtSeq = dynamic_cast<RamSequence*>(stmtList.get()))) {
                stmtSeq->add(std::move(stmt));
            } else {
                stmtList = std::make_unique<RamSequence>(std::move(stmtList), std::move(stmt));
            }
        } else {
            stmtList = std::move(stmt);
        }
    }
}

/* utility for creating a reordering that moves an atom to the front */
std::unique_ptr<AstExecutionOrder> AstTranslator::createReordering(const AstClause& originalClause, size_t frontAtom, size_t version, size_t diffVersion) {
    // the strategy is as follows:
    // given an order [a,b,c,d,e], where we intend c to be at the front,
    // we create an order [c,b,a,d,e], where atoms up to c are in reverse order, and elements after c are in forward order

    // set an execution plan so the diff_plus version of the relation is evaluated first
    // get existing execution plan
    AstExecutionOrder originalOrder;
    bool hasOriginalOrder = false;

    if (originalClause.getExecutionPlan() != nullptr) {
        auto plan = originalClause.getExecutionPlan()->clone();

        if (plan->hasOrderFor(version, diffVersion)) {
            return std::unique_ptr<AstExecutionOrder>(plan->getOrderFor(version, diffVersion).clone());
        } else if (plan->hasOrderFor(version, 0)) {
            originalOrder = plan->getOrderFor(version, 0);

            // extend in the case of extra atoms
            for (int k = originalOrder.size(); k < originalClause.getAtoms().size(); k++) {
                originalOrder.appendAtomIndex(k + 1);
            }

            // return std::unique_ptr<AstExecutionOrder>(originalOrder.clone());

            hasOriginalOrder = true;
        }
    }

    if (!hasOriginalOrder) {
        for (size_t k = 0; k < originalClause.getAtoms().size(); k++) {
            originalOrder.appendAtomIndex(k + 1);
        }
    }

    // r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

    // std::cout << "trying to reorder: " << originalClause << ", originalOrder: " << originalOrder << ", frontAtom: " << frontAtom << std::endl;

    // find position in originalOrder of atomAtFront
    auto positionItr = std::find(originalOrder.begin(), originalOrder.end(), frontAtom);

    // ensure originalOrder contains the target atom
    assert(positionItr != originalOrder.end() && "cannot reorder if original order doesn't contain target first atom");

    size_t position = std::distance(originalOrder.begin(), positionItr);

    // create a reordering, which is naive and needs to be re-ordered later
    auto newOrder = std::make_unique<AstExecutionOrder>();

    // push front atom
    newOrder->appendAtomIndex(frontAtom);
    
    /*
    // push atoms after the front atom position
    for (size_t curPos = position + 1; curPos < originalOrder.size(); curPos++) {
        newOrder->appendAtomIndex(originalOrder[curPos]);
    }

    // push atoms before the front atom position
    for (size_t curPos = position - 1; curPos >= 0 && curPos < position; curPos--) {
        newOrder->appendAtomIndex(originalOrder[curPos]);
    }
    */

    for (size_t curPos = 0; curPos < originalOrder.size(); curPos++) {
        if (curPos != position) newOrder->appendAtomIndex(originalOrder[curPos]);
    }

    // reorder a copy of originalClause, this copy is used for a sips-based reordering
    auto originalClauseCopy = std::unique_ptr<AstClause>(originalClause.clone());

    std::vector<unsigned int> newOrderVector(newOrder->size());
    std::transform(newOrder->begin(), newOrder->end(), newOrderVector.begin(),
            [](unsigned int i) -> unsigned int { return i - 1; });

    originalClauseCopy->reorderAtoms(newOrderVector);

    // create a sips function
    auto sipsFunc = ReorderLiteralsTransformer::getSipsFunction("incremental-reordering");
    auto reordering = ReorderLiteralsTransformer::applySips(sipsFunc, originalClauseCopy->getAtoms());

    // put this into an AstExecutionOrder
    auto executionReordering = std::make_unique<AstExecutionOrder>();
    for (auto i : reordering) {
        executionReordering->appendAtomIndex((*newOrder)[i]);
    }

    // std::cout << "after sips: " << *executionReordering << std::endl;
    return executionReordering;
}

/** generate RAM code for a non-recursive relation */
std::unique_ptr<RamStatement> AstTranslator::translateNonRecursiveRelation(
        const AstRelation& rel, const RecursiveClauses* recursiveClauses) {
    /* start with an empty sequence */
    std::unique_ptr<RamStatement> res;

    // the ram table reference
    std::unique_ptr<RamRelationReference> rrel = translateRelation(&rel);

    // utility to convert a list of AstConstraints to a disjunction
    auto toAstDisjunction = [&](std::vector<AstConstraint*> constraints) -> std::unique_ptr<AstConstraint> {
        std::unique_ptr<AstConstraint> result;
        for (const auto& cur : constraints) {
            if (result == nullptr) {
                result = std::unique_ptr<AstConstraint>(cur->clone());
            } else {
                result = std::make_unique<AstDisjunctionConstraint>(std::move(result), std::unique_ptr<AstConstraint>(cur->clone()));
            }
        }
        return result;
    };

    /* iterate over all clauses that belong to the relation */
    for (AstClause* clause : rel.getClauses()) {
        // skip recursive rules
        if (recursiveClauses->recursive(clause)) {
            continue;
        }

        if (Global::config().has("incremental")) {
            // store previous count and current count to determine if the rule is insertion or deletion
            // auto prevCount = clause->getHead()->getArgument(rel.getArity() - 2);
            auto curCount = clause->getHead()->getArgument(rel.getArity() - 1);

            // these should not be nullptrs
            // auto prevCountNum = dynamic_cast<AstNumberConstant*>(prevCount);
            auto curCountNum = dynamic_cast<AstNumberConstant*>(curCount);

            std::unique_ptr<RamStatement> rule;

            if (/*prevCountNum == nullptr ||*/ curCountNum == nullptr) {
                if (rel.getName().getName().find("@info") != std::string::npos) {
                    std::cout << "translating info rule: " << *clause << std::endl;
                    std::unique_ptr<RamStatement> rule;
                    // translate clause
                    rule = ClauseTranslator(*this).translateClause(*clause, *clause);

                    // add logging
                    if (Global::config().has("profile")) {
                        const std::string& relationName = toString(rel.getName());
                        const SrcLocation& srcLocation = clause->getSrcLoc();
                        const std::string clauseText = stringify(toString(*clause));
                        const std::string logTimerStatement =
                                LogStatement::tNonrecursiveRule(relationName, srcLocation, clauseText);
                        const std::string logSizeStatement =
                                LogStatement::nNonrecursiveRule(relationName, srcLocation, clauseText);
                        rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                logTimerStatement, std::unique_ptr<RamRelationReference>(rrel->clone())));
                    }

                    // add debug info
                    std::ostringstream ds;
                    ds << toString(*clause) << "\nin file ";
                    ds << clause->getSrcLoc();
                    rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                    // add rule to result
                    appendStmt(res, std::move(rule));
                } else {
                    std::cerr << "count annotations are not intialized!" << std::endl;
                }
            } else {

                nameUnnamedVariables(clause);

                // check if this clause is re-inserting hidden tuples
                // bool isReinsertionRule = (*prevCountNum == AstNumberConstant(1) && *curCountNum == AstNumberConstant(1));
                bool isReinsertionRule = *curCountNum == AstNumberConstant(2);
                bool isInsertionRule = (*curCountNum == AstNumberConstant(1)) && !isReinsertionRule;
                bool isDeletionRule = (*curCountNum == AstNumberConstant(-1));

                const auto& atoms = clause->getAtoms();
                const auto& negations = clause->getNegations();

                if (isReinsertionRule) {
                    // the reinsertion rule shouldn't exist for non-recursive rules, as all iteration numbers are 0 anyway
                    // so we can't have the situation of a tuple being deleted in iteration i and reinserted in iteration k > i
                } else {
                    if (isInsertionRule) {
                        // for (size_t i = 0; i < atoms.size(); i++) {
                        size_t i = 0;
                        // an insertion rule should look as follows:
                        // diff_plus_R :- diff_applied_R_1, diff_applied_R_2, ..., diff_plus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n
                        auto cl = clause->clone();

                        // set the head of the rule to be the diff relation
                        cl->getHead()->setName(translateDiffAppliedRelation(&rel)->get()->getName());

                        if (i < atoms.size()) {
                            /*
                            // ensure i-th tuple did not exist previously, this prevents double insertions
                            auto noPrevious = atoms[i]->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                            */

                            // the current version of the rule should have diff_plus_count in the i-th position
                            // cl->getAtoms()[i]->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            cl->getAtoms()[i]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            /*
                            cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));
                                        */

                            cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                            /*
                            for (size_t j = 0; j < i; j++) {
                                cl->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // cl->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious)));
                            }
                            */

                            for (size_t j = i + 1; j < atoms.size(); j++) {
                                // cl->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                cl->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            for (size_t j = 0; j < atoms.size(); j++) {
                                // add a constraint saying that the delta tuple can't have existed previously
                                auto noPrior = atoms[j]->clone();
                                noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                            }

                            cl->clearNegations();

                            // std::cout << "non-recursive: " << *cl << std::endl;

                            // translate cl
                            std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*cl, *clause, 0, 0);

                            // add logging
                            if (Global::config().has("profile")) {
                                const std::string& relationName = toString(rel.getName());
                                const SrcLocation& srcLocation = cl->getSrcLoc();
                                const std::string clText = stringify(toString(*cl));
                                const std::string logTimerStatement =
                                        LogStatement::tNonrecursiveRule(relationName, srcLocation, clText);
                                const std::string logSizeStatement =
                                        LogStatement::nNonrecursiveRule(relationName, srcLocation, clText);
                                rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                        logTimerStatement, std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(&rel)->clone())));
                            }

                            // add debug info
                            std::ostringstream ds;
                            ds << toString(*cl) << "\nin file ";
                            ds << cl->getSrcLoc();
                            rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                            // add rule to result
                            appendStmt(res, std::move(rule));
                        } else {
                            std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*cl, *clause);

                            // add logging
                            if (Global::config().has("profile")) {
                                const std::string& relationName = toString(rel.getName());
                                const SrcLocation& srcLocation = clause->getSrcLoc();
                                const std::string clauseText = stringify(toString(*cl));
                                const std::string logTimerStatement =
                                    LogStatement::tNonrecursiveRule(relationName, srcLocation, clauseText);
                                const std::string logSizeStatement =
                                    LogStatement::nNonrecursiveRule(relationName, srcLocation, clauseText);
                                rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(rrel->clone())));
                            }

                            // add debug info
                            std::ostringstream ds;
                            ds << toString(*cl) << "\nin file ";
                            ds << clause->getSrcLoc();
                            rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                            // add rule to result
                            appendStmt(res, std::move(rule));
                        }
                    }
                }
            }
        } else {
            std::unique_ptr<RamStatement> rule;
            if (Global::config().has("incremental")) {
            } else {
                // translate clause
                rule = ClauseTranslator(*this).translateClause(*clause, *clause);
            }

            // add logging
            if (Global::config().has("profile")) {
                const std::string& relationName = toString(rel.getName());
                const SrcLocation& srcLocation = clause->getSrcLoc();
                const std::string clauseText = stringify(toString(*clause));
                const std::string logTimerStatement =
                        LogStatement::tNonrecursiveRule(relationName, srcLocation, clauseText);
                const std::string logSizeStatement =
                        LogStatement::nNonrecursiveRule(relationName, srcLocation, clauseText);
                rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                        logTimerStatement, std::unique_ptr<RamRelationReference>(rrel->clone())));
            }

            // add debug info
            std::ostringstream ds;
            ds << toString(*clause) << "\nin file ";
            ds << clause->getSrcLoc();
            rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

            // add rule to result
            appendStmt(res, std::move(rule));
        }
    }

    // add logging for entire relation
    if (Global::config().has("profile")) {
        const std::string& relationName = toString(rel.getName());
        const SrcLocation& srcLocation = rel.getSrcLoc();
        const std::string logSizeStatement = LogStatement::nNonrecursiveRelation(relationName, srcLocation);

        // add timer if we did any work
        if (res) {
            const std::string logTimerStatement =
                    LogStatement::tNonrecursiveRelation(relationName, srcLocation);
            res = std::make_unique<RamLogRelationTimer>(
                    std::move(res), logTimerStatement, std::unique_ptr<RamRelationReference>(rrel->clone()));
        } else {
            // add table size printer
            appendStmt(res, std::make_unique<RamLogSize>(
                                    std::unique_ptr<RamRelationReference>(rrel->clone()), logSizeStatement));
        }
    }

    // done
    return res;
}

/** generate RAM code for a non-recursive relation */
std::unique_ptr<RamStatement> AstTranslator::translateUpdateNonRecursiveRelation(
        const AstRelation& rel, const RecursiveClauses* recursiveClauses) {
    /* start with an empty sequence */
    std::unique_ptr<RamStatement> res;

    // the ram table reference
    std::unique_ptr<RamRelationReference> rrel = translateRelation(&rel);

    // utility to convert a list of AstConstraints to a disjunction
    auto toAstDisjunction = [&](std::vector<AstConstraint*> constraints) -> std::unique_ptr<AstConstraint> {
        std::unique_ptr<AstConstraint> result;
        for (const auto& cur : constraints) {
            if (result == nullptr) {
                result = std::unique_ptr<AstConstraint>(cur->clone());
            } else {
                result = std::make_unique<AstDisjunctionConstraint>(std::move(result), std::unique_ptr<AstConstraint>(cur->clone()));
            }
        }
        return result;
    };

    // a mapper to name unnamed variables
    struct UnnamedVariableRenamer : public AstNodeMapper {
        mutable int counter = 0;

        UnnamedVariableRenamer() = default;

        std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
            // apply recursive
            node->apply(*this);

            // replace unknown variables
            if (dynamic_cast<AstUnnamedVariable*>(node.get())) {
                auto name = " _unnamed_negation_var" + toString(++counter);
                return std::make_unique<AstVariable>(name);
            }

            // otherwise nothing
            return node;
        }
    };


    /* iterate over all clauses that belong to the relation */
    for (AstClause* clause : rel.getClauses()) {
        // skip recursive rules
        if (recursiveClauses->recursive(clause)) {
            continue;
        }

        if (Global::config().has("incremental")) {
            // store previous count and current count to determine if the rule is insertion or deletion
            // auto prevCount = clause->getHead()->getArgument(rel.getArity() - 2);
            auto curCount = clause->getHead()->getArgument(rel.getArity() - 1);

            // these should not be nullptrs
            // auto prevCountNum = dynamic_cast<AstNumberConstant*>(prevCount);
            auto curCountNum = dynamic_cast<AstNumberConstant*>(curCount);

            if (/*prevCountNum == nullptr ||*/ curCountNum == nullptr) {
                if (rel.getName().getName().find("@info") != std::string::npos) {
                    // do nothing for info relations
                    continue;
                } else {
                    std::cerr << "count annotations are not intialized!" << std::endl;
                }
            }

            nameUnnamedVariables(clause);

            // check if this clause is re-inserting hidden tuples
            // bool isReinsertionRule = (*prevCountNum == AstNumberConstant(1) && *curCountNum == AstNumberConstant(1));
            bool isReinsertionRule = *curCountNum == AstNumberConstant(2);
            bool isInsertionRule = (*curCountNum == AstNumberConstant(1)) && !isReinsertionRule;
            bool isDeletionRule = (*curCountNum == AstNumberConstant(-1));

            const auto& atoms = clause->getAtoms();
            const auto& negations = clause->getNegations();

            std::unique_ptr<RamStatement> rule;

            if (isReinsertionRule) {
                // the reinsertion rule shouldn't exist for non-recursive rules, as all iteration numbers are 0 anyway
                // so we can't have the situation of a tuple being deleted in iteration i and reinserted in iteration k > i
            } else {
                if (isInsertionRule) {
                    for (size_t i = 0; i < atoms.size(); i++) {
                        // an insertion rule should look as follows:
                        // diff_plus_R :- diff_applied_R_1, diff_applied_R_2, ..., diff_plus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n
                        auto cl = clause->clone();

                        // set the head of the rule to be the diff relation
                        cl->getHead()->setName(translateDiffPlusRelation(&rel)->get()->getName());

                        /*
                        // ensure i-th tuple did not exist previously, this prevents double insertions
                        auto noPrevious = atoms[i]->clone();
                        noPrevious->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());
                        noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                        // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                        cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                        */

                        // the current version of the rule should have diff_plus_count in the i-th position
                        // cl->getAtoms()[i]->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                        cl->getAtoms()[i]->setName(translateActualDiffPlusRelation(getAtomRelation(atoms[i], program))->get()->getName());

                        /*
                        cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                    std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                    std::make_unique<AstNumberConstant>(0)));
                                    */

                        cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                    std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                    std::make_unique<AstNumberConstant>(0)));

                        // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                        for (size_t j = 0; j < i; j++) {
                            cl->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                            // ensure tuple is not actually inserted
                            auto curAtom = atoms[j]->clone();
                            // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                            // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                            // also ensure tuple existed previously
                            auto noPrevious = atoms[j]->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            // cl->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious)));
                        }

                        for (size_t j = i + 1; j < atoms.size(); j++) {
                            cl->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        }

                        for (size_t j = 0; j < atoms.size(); j++) {
                            // add a constraint saying that the tuples must have existed previously
                            cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));
                        }

                        // process negations
                        for (size_t j = 0; j < negations.size(); j++) {
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            auto negatedAtom = negations[j]->getAtom()->clone();
                            negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                        }

                        for (size_t j = 0; j < atoms.size(); j++) {
                            // add a constraint saying that the delta tuple can't have existed previously
                            auto noPrior = atoms[j]->clone();
                            noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                        }

                        cl->clearNegations();

                        // set an execution plan so the diff_plus version of the relation is evaluated first
                        auto plan = std::make_unique<AstExecutionPlan>();
                        auto order = std::make_unique<AstExecutionOrder>();
                        for (unsigned int j = 0; j < cl->getAtoms().size(); j++) {
                            order->appendAtomIndex(j + 1);
                        }

                        plan->setOrderFor(0, i + 1, std::move(createReordering(*cl, i + 1, 0, i + 1)));
                        cl->setExecutionPlan(std::move(plan));

                        // std::cout << "non-recursive: " << *cl << std::endl;

                        // translate cl
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*cl, *clause, 0, i + 1);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel.getName());
                            const SrcLocation& srcLocation = cl->getSrcLoc();
                            const std::string clText = stringify(toString(*cl));
                            const std::string logTimerStatement =
                                    LogStatement::tNonrecursiveRule(relationName, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nNonrecursiveRule(relationName, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(&rel)->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*cl) << "\nin file ";
                        ds << cl->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(res, std::move(rule));
                    }

                    // TODO: if there is a negation, then we need to add a version of the rule which applies when only the negations apply
                    for (size_t i = 0; i < negations.size(); i++) {
                        // an insertion rule should look as follows:
                        // diff_plus_R :- diff_applied_R_1, diff_applied_R_2, ..., diff_plus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                        auto cl = clause->clone();

                        // set the head of the rule to be the diff relation
                        cl->getHead()->setName(translateDiffPlusRelation(&rel)->get()->getName());

                        // clone the i-th negation's atom
                        // each negation needs to have either not existed, or be deleted
                        // for the non-existence case, we use a positive negation instead
                        auto negatedAtomNamed = negations[i]->getAtom()->clone();
                        /*
                        UnnamedVariableRenamer renamer;
                        negatedAtomNamed->apply(renamer);
                        */

                        auto negatedAtom = negatedAtomNamed->clone();
                        // negatedAtom->setName(translateDiffMinusCountRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        negatedAtom->setName(translateActualDiffMinusRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstVariable>("@negation_count"));
                        // negatedAtom->setArgument(negatedAtom->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                        negatedAtom->setArgument(negatedAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                        cl->addToBody(std::unique_ptr<AstAtom>(negatedAtom));

                        cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                    std::make_unique<AstVariable>("@negation_count"),
                                    std::make_unique<AstNumberConstant>(0)));

                        /*
                        // prevent double insertions across epochs
                        auto noPrevious = negatedAtomNamed->clone();
                        noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(noPrevious, program))->get()->getName());
                        noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                        // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                        cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                        */

                        // atoms before the i-th position should not fulfill the conditions for incremental deletion, otherwise we will have double insertions
                        for (size_t j = 0; j < i; j++) {
                            // cl->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            // ensure tuple is not actually inserted
                            auto curAtom = negations[j]->getAtom()->clone();
                            // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(curAtom, program))->get()->getName());
                            curAtom->setName(translateDiffMinusRelation(getAtomRelation(curAtom, program))->get()->getName());

                            curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                            // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                            // also ensure tuple existed previously
                            auto noPrevious = negations[j]->getAtom()->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(noPrevious, program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            // cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));
                        }

                        // process negations
                        for (size_t j = 0; j < negations.size(); j++) {
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            AstAtom* negatedAtom;
                            /*
                            if (j == i) {
                                negatedAtom = negatedAtomNamed->clone();
                            } else {
                            */
                                negatedAtom = negations[j]->getAtom()->clone();
                            //}
                            negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                        }

                        // the base relation for addition should be diff_applied, so translate each positive atom to the diff applied version
                        for (size_t j = 0; j < atoms.size(); j++) {
                            cl->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                            // we only insert a new tuple if other rules are not handling the insertion already
                            // ensure tuple is not actually inserted
                            auto curAtom = atoms[j]->clone();
                            // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                            // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                            // also ensure tuple existed previously
                            auto noPrevious = atoms[j]->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            // cl->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious)));
                            
                            // add a constraint saying that the tuples must have existed previously
                            cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // add a constraint saying that the delta tuple can't have existed previously
                            auto noPrior = atoms[j]->clone();
                            noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                        }

                        cl->clearNegations();

                        // set an execution plan so the diff_plus version of the relation is evaluated first
                        auto plan = std::make_unique<AstExecutionPlan>();
                        auto order = std::make_unique<AstExecutionOrder>();
                        for (unsigned int j = 0; j < cl->getAtoms().size(); j++) {
                            order->appendAtomIndex(j + 1);
                        }

                        plan->setOrderFor(0, atoms.size() + 1, std::move(createReordering(*cl, atoms.size() + 1, 0, atoms.size() + 1)));
                        cl->setExecutionPlan(std::move(plan));

                        // std::cout << "non-recursive: " << *cl << std::endl;

                        // translate cl
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*cl, *clause, 0, atoms.size() + i + 1);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel.getName());
                            const SrcLocation& srcLocation = cl->getSrcLoc();
                            const std::string clText = stringify(toString(*cl));
                            const std::string logTimerStatement =
                                    LogStatement::tNonrecursiveRule(relationName, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nNonrecursiveRule(relationName, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(&rel)->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*cl) << "\nin file ";
                        ds << cl->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(res, std::move(rule));
                    }
                } else if (isDeletionRule) {
                    for (size_t i = 0; i < atoms.size(); i++) {
                        // a deletion rule should look as follows:
                        // diff_minus_R :- R_1, R_2, ..., diff_minus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                        auto cl = clause->clone();

                        // set the head of the rule to be the diff relation
                        cl->getHead()->setName(translateDiffMinusRelation(&rel)->get()->getName());

                        /*
                        // ensure i-th tuple did not exist previously, this prevents double insertions
                        auto noPrevious = atoms[i]->clone();
                        noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());
                        noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                        // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                        cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                        */

                        // the current version of the rule should have diff_minus_count in the i-th position
                        // cl->getAtoms()[i]->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                        cl->getAtoms()[i]->setName(translateActualDiffMinusRelation(getAtomRelation(atoms[i], program))->get()->getName());

                        /*
                        cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                    std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                    std::make_unique<AstNumberConstant>(0)));
                                    */

                        cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                    std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                    std::make_unique<AstNumberConstant>(0)));

                        // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                        for (size_t j = 0; j < i; j++) {
                            // cl->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            // ensure tuple is not actually inserted
                            auto curAtom = atoms[j]->clone();
                            // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            curAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());

                            curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                            // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                            // also ensure tuple existed previously
                            auto noPrevious = atoms[j]->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            // cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));
                        }

                        for (size_t j = i + 1; j < atoms.size(); j++) {
                            // cl->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            // standard relation has the same tuples as diff_minus_applied, just with different counts
                            cl->getAtoms()[j]->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        }

                        for (size_t j = 0; j < atoms.size(); j++) {
                            // add a constraint saying that the tuples must have existed previously
                            if (j != i) {
                                cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                            std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                            std::make_unique<AstNumberConstant>(0)));
                            }

                            // add a constraint saying that the delta tuple can't have existed previously
                            auto noPrior = atoms[j]->clone();
                            // noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                        }


                        // process negations
                        for (size_t j = 0; j < negations.size(); j++) {
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            auto negatedAtom = negations[j]->getAtom()->clone();
                            // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                        }

                        cl->clearNegations();

                        // set an execution plan so the diff_minus version of the relation is evaluated first
                        auto plan = std::make_unique<AstExecutionPlan>();
                        auto order = std::make_unique<AstExecutionOrder>();
                        for (unsigned int j = 0; j < cl->getAtoms().size(); j++) {
                            order->appendAtomIndex(j + 1);
                        }

                        plan->setOrderFor(0, i + 1, std::move(createReordering(*cl, i + 1, 0, i + 1)));
                        cl->setExecutionPlan(std::move(plan));

                        // std::cout << "non-recursive: " << *cl << std::endl;

                        // translate cl
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*cl, *clause, 0, i + 1);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel.getName());
                            const SrcLocation& srcLocation = cl->getSrcLoc();
                            const std::string clText = stringify(toString(*cl));
                            const std::string logTimerStatement =
                                    LogStatement::tNonrecursiveRule(relationName, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nNonrecursiveRule(relationName, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(&rel)->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*cl) << "\nin file ";
                        ds << cl->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(res, std::move(rule));
                    }

                    // TODO: if there is a negation, then we need to add a version of the rule which applies when only the negations apply
                    for (size_t i = 0; i < negations.size(); i++) {
                        // an insertion rule should look as follows:
                        // diff_minus_R :- R_1, R_2, ..., diff_minus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                        auto cl = clause->clone();

                        // set the head of the rule to be the diff relation
                        cl->getHead()->setName(translateDiffMinusRelation(&rel)->get()->getName());

                        // clone the i-th negation's atom
                        // each negation needs to have either not existed, or be deleted
                        // for the non-existence case, we use a positive negation instead
                        auto negatedAtomNamed = negations[i]->getAtom()->clone();
                        /*
                        UnnamedVariableRenamer renamer;
                        negatedAtomNamed->apply(renamer);
                        */

                        auto negatedAtom = negatedAtomNamed->clone();
                        // negatedAtom->setName(translateDiffPlusCountRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        negatedAtom->setName(translateActualDiffPlusRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        // negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                        negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstVariable>("@negation_count"));
                        negatedAtom->setArgument(negatedAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                        // negatedAtom->setArgument(negatedAtom->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                        cl->addToBody(std::unique_ptr<AstAtom>(negatedAtom));

                        cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                    std::make_unique<AstVariable>("@negation_count"),
                                    std::make_unique<AstNumberConstant>(0)));

                        /*
                        // prevent double insertions across epochs
                        auto noPrevious = negatedAtomNamed->clone();
                        noPrevious->setName(translateRelation(getAtomRelation(noPrevious, program))->get()->getName());
                        noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                        // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                        cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                        */

                        // atoms before the i-th position should not fulfill the conditions for incremental deletion, otherwise we will have double insertions
                        for (size_t j = 0; j < i; j++) {
                            // cl->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            // ensure tuple is actually inserted
                            auto curAtom = negations[j]->getAtom()->clone();
                            // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(curAtom, program))->get()->getName());
                            curAtom->setName(translateDiffPlusRelation(getAtomRelation(curAtom, program))->get()->getName());

                            curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                            // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                            // also ensure tuple existed previously
                            auto noPrevious = negations[j]->getAtom()->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(noPrevious, program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            // cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));
                        }

                        // process negations
                        for (size_t j = 0; j < negations.size(); j++) {
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            AstAtom* negatedAtom;
                            /*
                            if (j == i) {
                                negatedAtom = negatedAtomNamed->clone();
                            } else {
                            */
                                negatedAtom = negations[j]->getAtom()->clone();
                            // }
                            // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                        }

                        for (size_t j = 0; j < atoms.size(); j++) {
                            // ensure tuple is not actually inserted
                            auto curAtom = atoms[j]->clone();
                            // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            curAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());

                            curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                            // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                            // also ensure tuple existed previously
                            auto noPrevious = atoms[j]->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            cl->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            // cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));

                            // ensure the tuple existed previously
                            cl->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // add a constraint saying that the delta tuple can't have existed previously
                            auto noPrior = atoms[j]->clone();
                            // noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                            cl->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                        }

                        cl->clearNegations();

                        // set an execution plan so the diff_minus version of the relation is evaluated first
                        auto plan = std::make_unique<AstExecutionPlan>();
                        auto order = std::make_unique<AstExecutionOrder>();
                        for (unsigned int j = 0; j < cl->getAtoms().size(); j++) {
                            order->appendAtomIndex(j + 1);
                        }

                        plan->setOrderFor(0, atoms.size() + 1, std::move(createReordering(*cl, atoms.size() + 1, 0, atoms.size() + 1)));
                        cl->setExecutionPlan(std::move(plan));

                        // std::cout << "non-recursive: " << *cl << std::endl;

                        // translate cl
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*cl, *clause, 0, atoms.size() + i + 1);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel.getName());
                            const SrcLocation& srcLocation = cl->getSrcLoc();
                            const std::string clText = stringify(toString(*cl));
                            const std::string logTimerStatement =
                                    LogStatement::tNonrecursiveRule(relationName, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nNonrecursiveRule(relationName, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(&rel)->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*cl) << "\nin file ";
                        ds << cl->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(res, std::move(rule));
                    }
                }
            }
        } else {
            std::unique_ptr<RamStatement> rule;
            if (Global::config().has("incremental")) {
            } else {
                // translate clause
                rule = ClauseTranslator(*this).translateClause(*clause, *clause);
            }

            // add logging
            if (Global::config().has("profile")) {
                const std::string& relationName = toString(rel.getName());
                const SrcLocation& srcLocation = clause->getSrcLoc();
                const std::string clauseText = stringify(toString(*clause));
                const std::string logTimerStatement =
                        LogStatement::tNonrecursiveRule(relationName, srcLocation, clauseText);
                const std::string logSizeStatement =
                        LogStatement::nNonrecursiveRule(relationName, srcLocation, clauseText);
                rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                        logTimerStatement, std::unique_ptr<RamRelationReference>(rrel->clone())));
            }

            // add debug info
            std::ostringstream ds;
            ds << toString(*clause) << "\nin file ";
            ds << clause->getSrcLoc();
            rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

            // add rule to result
            appendStmt(res, std::move(rule));
        }
    }

    // add logging for entire relation
    if (Global::config().has("profile")) {
        const std::string& relationName = toString(rel.getName());
        const SrcLocation& srcLocation = rel.getSrcLoc();
        const std::string logSizeStatement = LogStatement::nNonrecursiveRelation(relationName, srcLocation);

        // add timer if we did any work
        if (res) {
            const std::string logTimerStatement =
                    LogStatement::tNonrecursiveRelation(relationName, srcLocation);
            res = std::make_unique<RamLogRelationTimer>(
                    std::move(res), logTimerStatement, std::unique_ptr<RamRelationReference>(rrel->clone()));
        } else {
            // add table size printer
            appendStmt(res, std::make_unique<RamLogSize>(
                                    std::unique_ptr<RamRelationReference>(rrel->clone()), logSizeStatement));
        }
    }

    // done
    return res;
}

/**
 * A utility function assigning names to unnamed variables such that enclosing
 * constructs may be cloned without losing the variable-identity.
 */
void AstTranslator::nameUnnamedVariables(AstClause* clause) {
    // the node mapper conducting the actual renaming
    struct Instantiator : public AstNodeMapper {
        mutable int counter = 0;

        Instantiator() = default;

        std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
            // apply recursive
            node->apply(*this);

            // replace unknown variables
            if (dynamic_cast<AstUnnamedVariable*>(node.get())) {
                auto name = " _unnamed_var" + toString(++counter);
                return std::make_unique<AstVariable>(name);
            }

            // otherwise nothing
            return node;
        }
    };

    // name all variables in the atoms
    Instantiator init;
    for (auto& atom : clause->getAtoms()) {
        atom->apply(init);
    }
}


/** generate RAM code for recursive relations in a strongly-connected component */
std::unique_ptr<RamStatement> AstTranslator::translateRecursiveRelation(
        const std::set<const AstRelation*>& scc, const RecursiveClauses* recursiveClauses, int indexOfScc) {
    // initialize sections
    std::unique_ptr<RamStatement> preamble;
    std::unique_ptr<RamSequence> clearTable(new RamSequence());
    std::unique_ptr<RamSequence> updateTable(new RamSequence());
    std::unique_ptr<RamStatement> postamble;

    // --- create preamble ---

    // mappings for temporary relations
    std::map<const AstRelation*, std::unique_ptr<RamRelationReference>> rrel;
    std::map<const AstRelation*, std::unique_ptr<RamRelationReference>> relDelta;
    std::map<const AstRelation*, std::unique_ptr<RamRelationReference>> relNew;

    // utility to convert a list of AstConstraints to a disjunction
    auto toAstDisjunction = [&](std::vector<AstConstraint*> constraints) -> std::unique_ptr<AstConstraint> {
        std::unique_ptr<AstConstraint> result;
        for (const auto& cur : constraints) {
            if (result == nullptr) {
                result = std::unique_ptr<AstConstraint>(cur->clone());
            } else {
                result = std::make_unique<AstDisjunctionConstraint>(std::move(result), std::unique_ptr<AstConstraint>(cur->clone()));
            }
        }
        return result;
    };

    /* Compute non-recursive clauses for relations in scc and push
       the results in their delta tables. */
    for (const AstRelation* rel : scc) {

        std::unique_ptr<RamStatement> updateRelTable;
        std::unique_ptr<RamStatement> clearRelTable;

        /* create two temporary tables for relaxed semi-naive evaluation */
        rrel[rel] = translateRelation(rel);
        relDelta[rel] = translateDeltaRelation(rel);
        relNew[rel] = translateNewRelation(rel);

        /* create update statements for fixpoint (even iteration) */
        if (!Global::config().has("incremental")) {
            appendStmt(updateRelTable,
                    std::make_unique<RamSequence>(
                            std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(rrel[rel]->clone()),
                                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone())),
                            std::make_unique<RamSwap>(
                                    std::unique_ptr<RamRelationReference>(relDelta[rel]->clone()),
                                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone())),
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone()))));

        } else {
            appendStmt(updateRelTable,
                    std::make_unique<RamSequence>(
                        /*
                            // populate the diff minus relations
                            // merge new_diff_minus into diff_minus to update with new tuples from current iteration
                            std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())),
                                    */

                            // update the diff plus relations
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone())),

                            std::make_unique<RamExistingMerge>(std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone())),

                            // merge new_diff_plus into diff_plus to update with new tuples from current iteration
                            std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone())),


                            /*
                            std::make_unique<RamSwap>(std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone())),
                                    */

                            /*
                            // update the diff applied relations
                            // assume diff_applied contains all correct tuples from previous epoch
                            // merge new_diff_minus and new_diff_plus into diff_plus_applied to update with new tuples from current iteration
                            // order is important - minus should be applied before plus,
                            // as plus may be able to update tuples that are deleted in the current epoch
                            std::make_unique<RamMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())),
                            std::make_unique<RamMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())),
                                    */

                /*
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())),
                                    */
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone()))));
        }

        /* measure update time for each relation */
        if (Global::config().has("profile")) {
            updateRelTable = std::make_unique<RamLogRelationTimer>(std::move(updateRelTable),
                    LogStatement::cRecursiveRelation(toString(rel->getName()), rel->getSrcLoc()),
                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone()));
        }


        if (Global::config().has("incremental")) {
            appendStmt(postamble, std::make_unique<RamSequence>(
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone())),
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone()))));
        } else {
            /* drop temporary tables after recursion */
            appendStmt(postamble, std::make_unique<RamSequence>(
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(relDelta[rel]->clone())),
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(relNew[rel]->clone()))));
        }


        /* Generate code for non-recursive part of relation */
        appendStmt(preamble, translateNonRecursiveRelation(*rel, recursiveClauses));

        if (Global::config().has("incremental")) {
            // update the diff applied relations
            // merge the full relation into diff_applied
            // merge new_diff_minus and new_diff_plus into diff_plus_applied to update with new tuples from current iteration
            // order is important - minus should be applied before plus,
            // as plus may be able to update tuples that are deleted in the current epoch
            /*
            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone())));
            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone())));
                            */

            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone())));

        } else {

            /* Generate merge operation for temp tables */
            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(relDelta[rel]->clone()),
                        std::unique_ptr<RamRelationReference>(rrel[rel]->clone())));
        }

        /* Add update operations of relations to parallel statements */
        updateTable->add(std::move(updateRelTable));
        clearTable->add(std::move(clearRelTable));
    }

    // for incremental, create a temporary table storing the max iteration number in the current SCC
    // we want the relation to have a single fact, like
    // @max_iter_scc_i(
    //   max(
    //     max @iter : rel_1(_, _, @iter, _, _), 
    //     max @iter : rel_2(_, _, @iter, _, _),
    //     ...)).
    auto maxIterRelation = new RamRelation("scc_" + std::to_string(indexOfScc) + "_@max_iter", 1, 1, std::vector<std::string>({"max_iter"}), std::vector<std::string>({"s"}), RelationRepresentation::DEFAULT);
    auto maxIterRelationRef = std::make_unique<RamRelationReference>(maxIterRelation);

    if (Global::config().has("incremental")) {
        appendStmt(preamble, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(maxIterRelationRef->clone())));

        // we make the final project first
        std::vector<std::unique_ptr<RamExpression>> maxIterNumbers;
        int ident = 0;
        for (const AstRelation* rel : scc) {
            maxIterNumbers.push_back(std::make_unique<RamTupleElement>(ident, 0));
            ident++;
        }
        auto maxIterNumber = std::make_unique<RamIntrinsicOperator>(FunctorOp::MAX, std::move(maxIterNumbers));

        // create a set of aggregates over the relations in the scc
        // a RamAggregate is a nested structure
        std::vector<std::unique_ptr<RamExpression>> maxIterNumFunctor;
        maxIterNumFunctor.push_back(std::move(maxIterNumber));
        std::unique_ptr<RamOperation> outerMaxIterAggregate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(maxIterRelationRef->clone()), std::move(maxIterNumFunctor));

        ident = 0;
        for (const AstRelation* rel : scc) {
            outerMaxIterAggregate = std::make_unique<RamAggregate>(std::move(outerMaxIterAggregate), AggregateFunction::MAX, std::unique_ptr<RamRelationReference>(rrel[rel]->clone()), std::make_unique<RamTupleElement>(ident, rrel[rel]->get()->getArity() - 2), std::make_unique<RamTrue>(), ident);
            ident++;
        }

        appendStmt(preamble, std::make_unique<RamQuery>(std::move(outerMaxIterAggregate)));
    }

    // --- build main loop ---

    std::unique_ptr<RamParallel> loopSeq(new RamParallel());

    // create a utility to check SCC membership
    auto isInSameSCC = [&](const AstRelation* rel) {
        return std::find(scc.begin(), scc.end(), rel) != scc.end();
    };

    /* Compute temp for the current tables */
    for (const AstRelation* rel : scc) {
        std::unique_ptr<RamStatement> loopRelSeq;

        /* Find clauses for relation rel */
        for (size_t i = 0; i < rel->clauseSize(); i++) {
            AstClause* cl = rel->getClause(i);

            // skip non-recursive clauses
            if (!recursiveClauses->recursive(cl)) {
                continue;
            }

            // each recursive rule results in several operations
            const auto& atoms = cl->getAtoms();
            const auto& negations = cl->getNegations();

            int version = 0;
            int diffVersion = 1;
            if (Global::config().has("incremental")) {
                // store previous count and current count to determine if the rule is insertion or deletion
                // auto prevCount = cl->getHead()->getArgument(rel->getArity() - 2);
                auto curCount = cl->getHead()->getArgument(rel->getArity() - 1);

                // these should not be nullptrs
                // auto prevCountNum = dynamic_cast<AstNumberConstant*>(prevCount);
                auto curCountNum = dynamic_cast<AstNumberConstant*>(curCount);

                if (/*prevCountNum == nullptr ||*/ curCountNum == nullptr) {
                    std::cerr << "count annotations are not intialized!" << std::endl;
                }

                nameUnnamedVariables(cl);

                // check if this clause is re-inserting hidden tuples
                // bool isReinsertionRule = (*prevCountNum == AstNumberConstant(1) && *curCountNum == AstNumberConstant(1));
                bool isReinsertionRule = *curCountNum == AstNumberConstant(2);
                bool isInsertionRule = (*curCountNum == AstNumberConstant(1)) && !isReinsertionRule;
                bool isDeletionRule = (*curCountNum == AstNumberConstant(-1));

                if (isReinsertionRule) {
                    /*
                    std::unique_ptr<AstClause> rdiff(cl->clone());

                    rdiff->getHead()->setName(translateNewDiffPlusRelation(rel)->get()->getName());

                    for (size_t k = 0; k < atoms.size(); k++) {
                        rdiff->getAtoms()[k]->setName(translateDiffAppliedRelation(getAtomRelation(rdiff->getAtoms()[k], program))->get()->getName());
                    }

                    // for incremental, we use iteration counts to simulate delta relation rather than explicitly having a separate relation
                    auto diffAppliedHeadAtom = cl->getHead()->clone();
                    diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                    // add constraints saying that each body tuple must have existed in the previous epoch
                    std::vector<AstConstraint*> existsReinsertion;

                    diffVersion = 1;
                    for (size_t i = 0; i < atoms.size(); i++) {
                        // ensure tuple actually existed
                        auto curAtom = atoms[i]->clone();
                        curAtom->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());

                        curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());

                        rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(curAtom)));
                    }

                    // if we have incremental evaluation, we use iteration counts to simulate delta relations
                    // rather than explicitly having a separate relation
                    rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                            std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                    // a tuple should only be reinserted if that tuple is deleted
                    auto deletedTuple = cl->getHead()->clone();
                    // deletedTuple->setName(translateDiffMinusCountRelation(rel)->get()->getName());
                    deletedTuple->setName(translateDiffMinusRelation(rel)->get()->getName());
                    deletedTuple->setArgument(deletedTuple->getArity() - 1, std::make_unique<AstVariable>("@deleted_count"));
                    deletedTuple->setArgument(deletedTuple->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                    deletedTuple->setArgument(deletedTuple->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                    rdiff->addToBody(std::unique_ptr<AstAtom>(deletedTuple));
                    rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE, std::make_unique<AstVariable>("@deleted_count"), std::make_unique<AstNumberConstant>(0)));

                    std::vector<std::unique_ptr<AstLiteral>> notDeletedChecks;

                    // process negations
                    for (size_t j = 0; j < negations.size(); j++) {
                        // each negation needs to have either not existed, or be deleted
                        // for the non-existence case, we use a positive negation instead
                        auto negatedAtom = negations[j]->getAtom()->clone();
                        negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));

                        // negations shouldn't exist in diff_minus_count, otherwise they will be processed by insertion rules
                        auto notDeleted = negations[j]->getAtom()->clone();
                        // notDeleted->setName(translateDiffMinusCountRelation(getAtomRelation(notDeleted, program))->get()->getName());
                        notDeleted->setName(translateDiffMinusRelation(getAtomRelation(notDeleted, program))->get()->getName());
                        notDeleted->setArgument(notDeleted->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                        notDeleted->setArgument(notDeleted->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                        notDeleted->setArgument(notDeleted->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                        notDeletedChecks.push_back(std::make_unique<AstNegation>(std::unique_ptr<AstAtom>(notDeleted)));
                    }

                    rdiff->clearNegations();

                    for (auto& notDeleted : notDeletedChecks) {
                        rdiff->addToBody(std::move(notDeleted));
                    }

                    version = 0;
                    // use delta versions of relations for semi-naive evaluation
                    for (size_t j = 0; j < atoms.size(); j++) {
                        if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                            continue;
                        }

                        // create clone
                        std::unique_ptr<AstClause> r1(rdiff->clone());

                        // set the j-th atom to use DeltaDiffApplied
                        // r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        r1->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                    std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                        // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                        for (size_t k = j + 1; k < atoms.size(); k++) {
                            if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                            }
                        }

                        // reorder cl so that the deletedTuple atom is evaluated first
                        std::vector<unsigned int> reordering;
                        reordering.push_back(atoms.size());
                        for (int k = 0; k < atoms.size(); k++) {
                            reordering.push_back(k);
                        }
                        r1->reorderAtoms(reordering);


                        std::cout << "recursive: " << *r1 << std::endl;

                        // diffVersion = 0 here because the reinsertion rule doesn't really look like any other standard rule,
                        // and diffVersion shouldn't apply to this anyway
                        diffVersion = 0;

                        // translate rdiff
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel->getName());
                            const SrcLocation& srcLocation = r1->getSrcLoc();
                            const std::string clText = stringify(toString(*r1));
                            const std::string logTimerStatement =
                                    LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*r1) << "\nin file ";
                        ds << r1->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(loopRelSeq, std::move(rule));

                        version++;
                    }
                    */
                } else {
                    // AstAtom* atom = atoms[j];
                    // const AstRelation* atomRelation = getAtomRelation(atom, program);

                    // clone the clause so we can use diff and diff_applied auxiliary relations
                    // std::unique_ptr<AstClause> rdiff(cl->clone());

                    if (isInsertionRule) {
                        diffVersion = 0;
                        // for (size_t i = 0; i < atoms.size(); i++) {
                        size_t i = 0;
                        // an insertion rule should look as follows:
                        // R :- R_1, R_2, ..., diff_plus_count_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                        std::unique_ptr<AstClause> rdiff(cl->clone());

                        // set the head of the rule to be the diff relation
                        rdiff->getHead()->setName(translateDiffAppliedRelation(rel)->get()->getName());

                        if (i < atoms.size()) {

                            /*
                            // ensure i-th tuple did not exist previously, this prevents double insertions
                            auto noPrevious = atoms[i]->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                            */

                            // the current version of the rule should have diff_plus_count in the i-th position
                            // rdiff->getAtoms()[i]->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            rdiff->getAtoms()[i]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            /*
                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));
                                        */

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                            /*
                            for (size_t j = 0; j < i; j++) {
                                rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious)));
                            }
                            */

                            for (size_t j = i + 1; j < atoms.size(); j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            }


                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));

                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_plus
                            rdiff->getHead()->setName(translateNewDiffAppliedRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                /*
                                // add a constraint saying that tuple j should be in the previous iteration, simulating delta relations
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                            */
                                
                                // use delta_diff_applied relation
                                r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                // any atoms before atom j should be in earlier itereations, check this by a constraint on the iteration number
                                for (size_t k = 0; k < j; k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // for differential, only use earliest derivation of tuple
                                for (size_t k = 0; k < atoms.size(); k++) {
                                    if (k != j && isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        // add a constraint saying that the delta tuple can't have existed previously
                                        auto noPrior = atoms[k]->clone();
                                        noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[k], program))->get()->getName());
                                        noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                        r1->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                                    }
                                }

                                std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }
                            diffVersion++;
                        }
                        assert(cl->getExecutionPlan() == nullptr || version > cl->getExecutionPlan()->getMaxVersion());

                        // }

                        /*
                        diffVersion = atoms.size() + 1;
                        // TODO: if there is a negation, then we need to add a version of the rule which applies when only the negations apply
                        for (size_t i = 0; i < negations.size(); i++) {
                            // an insertion rule should look as follows:
                            // R :- R_1, R_2, ..., diff_plus_count_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            auto rdiff = cl->clone();

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffPlusRelation(rel)->get()->getName());

                            // clone the i-th negation's atom
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            auto negatedAtom = negations[i]->getAtom()->clone();
                            // negatedAtom->setName(translateDiffMinusCountRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            negatedAtom->setName(translateDiffMinusRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                            negatedAtom->setArgument(negatedAtom->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                            rdiff->addToBody(std::unique_ptr<AstAtom>(negatedAtom));

                            // prevent double insertions across epochs
                            auto noPrevious = negations[i]->getAtom()->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(noPrevious, program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));

                            // atoms before the i-th position should not fulfill the conditions for incremental deletion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = negations[j]->getAtom()->clone();
                                // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(curAtom, program))->get()->getName());
                                curAtom->setName(translateDiffMinusRelation(getAtomRelation(curAtom, program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                                curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                                // also ensure tuple existed previously
                                auto noPrevious = negations[j]->getAtom()->clone();
                                noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(noPrevious, program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            // the base relation for addition should be diff_applied, so translate each positive atom to the diff applied version
                            for (size_t j = 0; j < atoms.size(); j++) {
                                rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                                curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_plus
                            rdiff->getHead()->setName(translateNewDiffPlusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }
                            diffVersion++;
                        }
                        */
                    } else if (isDeletionRule) {
                        /*
                        diffVersion = 1;
                        for (size_t i = 0; i < atoms.size(); i++) {
                            // a deletion rule should look as follows:
                            // diff_minus_R :- R_1, R_2, ..., diff_minus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            std::unique_ptr<AstClause> rdiff(cl->clone());

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffMinusRelation(rel)->get()->getName());

                            // ensure i-th tuple did not exist previously, this prevents double insertions
                            auto noPrevious = atoms[i]->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));

                            // the current version of the rule should have diff_minus_count in the i-th position
                            // rdiff->getAtoms()[i]->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            rdiff->getAtoms()[i]->setName(translateDiffMinusRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                                curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            }

                            for (size_t j = i + 1; j < atoms.size(); j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                // standard relation has the same tuples as diff_minus_applied, just with different counts
                                rdiff->getAtoms()[j]->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            }


                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_minus
                            rdiff->getHead()->setName(translateNewDiffMinusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // tuple j should be in the previous iteration, simulating delta relations
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }

                            diffVersion++;
                        }

                        diffVersion = atoms.size() + 1;
                        // TODO: if there is a negation, then we need to add a version of the rule which applies when only the negations apply
                        for (size_t i = 0; i < negations.size(); i++) {
                            // an insertion rule should look as follows:
                            // R :- R_1, R_2, ..., diff_plus_count_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            auto rdiff = cl->clone();

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffMinusRelation(rel)->get()->getName());

                            // clone the i-th negation's atom
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            auto negatedAtom = negations[i]->getAtom()->clone();
                            // negatedAtom->setName(translateDiffPlusCountRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            negatedAtom->setName(translateDiffPlusRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                            negatedAtom->setArgument(negatedAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                            negatedAtom->setArgument(negatedAtom->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                            rdiff->addToBody(std::unique_ptr<AstAtom>(negatedAtom));

                            // prevent double insertions across epochs
                            auto noPrevious = negations[i]->getAtom()->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(noPrevious, program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));

                            // atoms before the i-th position should not fulfill the conditions for incremental deletion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = negations[j]->getAtom()->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(curAtom, program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(curAtom, program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                                curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = negations[j]->getAtom()->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(noPrevious, program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            for (size_t j = 0; j < atoms.size(); j++) {
                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                                curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_plus
                            rdiff->getHead()->setName(translateNewDiffMinusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // r1->getAtoms()[j]->setName(translateDeltaRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->getAtoms()[j]->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }
                            diffVersion++;
                        }
                        */
                    }
                }
            } else {
                version = 0;
                for (size_t j = 0; j < atoms.size(); ++j) {
                    AstAtom* atom = atoms[j];
                    const AstRelation* atomRelation = getAtomRelation(atom, program);

                    // only interested in atoms within the same SCC
                    if (!isInSameSCC(atomRelation)) {
                        continue;
                    }

                    // modify the processed rule to use relDelta and write to relNew
                    std::unique_ptr<AstClause> r1(cl->clone());
                    r1->getHead()->setName(relNew[rel]->get()->getName());
                    // if we have incremental evaluation, we use iteration counts to simulate delta relations
                    // rather than explicitly having a separate relation
                    if (!Global::config().has("incremental")) {
                        r1->getAtoms()[j]->setName(relDelta[atomRelation]->get()->getName());
                    }
                    if (Global::config().has("provenance")) {
                        size_t numberOfHeights = rel->numberOfHeightParameters();
                        r1->addToBody(std::make_unique<AstSubsumptionNegation>(
                                std::unique_ptr<AstAtom>(cl->getHead()->clone()), 1 + numberOfHeights));
                    } else {
                        if (r1->getHead()->getArity() > 0)
                            r1->addToBody(std::make_unique<AstNegation>(
                                    std::unique_ptr<AstAtom>(cl->getHead()->clone())));
                    }

                    // replace wildcards with variables (reduces indices when wildcards are used in recursive
                    // atoms)
                    nameUnnamedVariables(r1.get());

                    // reduce R to P ...
                    for (size_t k = j + 1; k < atoms.size(); k++) {
                        if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                            AstAtom* cur = r1->getAtoms()[k]->clone();
                            cur->setName(relDelta[getAtomRelation(atoms[k], program)]->get()->getName());
                            r1->addToBody(std::make_unique<AstNegation>(std::unique_ptr<AstAtom>(cur)));
                        }
                    }

                    std::unique_ptr<RamStatement> rule =
                            ClauseTranslator(*this).translateClause(*r1, *cl, version);

                    /* add logging */
                    if (Global::config().has("profile")) {
                        const std::string& relationName = toString(rel->getName());
                        const SrcLocation& srcLocation = cl->getSrcLoc();
                        const std::string clauseText = stringify(toString(*cl));
                        const std::string logTimerStatement =
                                LogStatement::tRecursiveRule(relationName, version, srcLocation, clauseText);
                        const std::string logSizeStatement =
                                LogStatement::nRecursiveRule(relationName, version, srcLocation, clauseText);
                        rule = std::make_unique<RamSequence>(
                                std::make_unique<RamLogRelationTimer>(std::move(rule), logTimerStatement,
                                        std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
                    }

                    // add debug info
                    std::ostringstream ds;
                    ds << toString(*cl) << "\nin file ";
                    ds << cl->getSrcLoc();
                    rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                    // add to loop body
                    appendStmt(loopRelSeq, std::move(rule));

                    // increment version counter
                    version++;
                }
                assert(cl->getExecutionPlan() == nullptr || version > cl->getExecutionPlan()->getMaxVersion());
            }
        }

        // if there was no rule, continue
        if (!loopRelSeq) {
            continue;
        }

        // label all versions
        if (Global::config().has("profile")) {
            const std::string& relationName = toString(rel->getName());
            const SrcLocation& srcLocation = rel->getSrcLoc();
            const std::string logTimerStatement = LogStatement::tRecursiveRelation(relationName, srcLocation);
            const std::string logSizeStatement = LogStatement::nRecursiveRelation(relationName, srcLocation);
            loopRelSeq = std::make_unique<RamLogRelationTimer>(std::move(loopRelSeq), logTimerStatement,
                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone()));
        }

        /* add rule computations of a relation to parallel statement */
        loopSeq->add(std::move(loopRelSeq));
    }

    /* construct exit conditions for odd and even iteration */
    auto addCondition = [](std::unique_ptr<RamCondition>& cond, std::unique_ptr<RamCondition> clause) {
        cond = ((cond) ? std::make_unique<RamConjunction>(std::move(cond), std::move(clause))
                       : std::move(clause));
    };

    std::unique_ptr<RamCondition> exitCond;
    for (const AstRelation* rel : scc) {
        if (Global::config().has("incremental")) {
            addCondition(exitCond, std::make_unique<RamEmptinessCheck>(
                                           std::unique_ptr<RamRelationReference>(translateNewDiffAppliedRelation(rel)->clone())));
            /*
            addCondition(exitCond, std::make_unique<RamEmptinessCheck>(
                                           std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())));
                                           */
        } else {
            addCondition(exitCond, std::make_unique<RamEmptinessCheck>(
                                           std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
        }
    }

    /*
    if (Global::config().has("incremental")) {
        ramProg->addSubroutine("scc_" + std::to_string(indexOfScc) + "_exit", makeIncrementalExitCondSubroutine(scc));
        std::vector<std::unique_ptr<RamExpression>> exitCondArgs;
        // exitCondArgs.push_back(std::make_unique<RamIterationNumber>());
        addCondition(exitCond, std::make_unique<RamSubroutineCondition>("scc_" + std::to_string(indexOfScc) + "_exit", std::move(exitCondArgs)));
    }
    */

    /* construct fixpoint loop  */
    std::unique_ptr<RamStatement> res;
    if (preamble) appendStmt(res, std::move(preamble));
    if (!loopSeq->getStatements().empty() && exitCond && clearTable && updateTable) {
        appendStmt(res, std::make_unique<RamLoop>(std::move(loopSeq), std::move(clearTable), 
                                std::make_unique<RamExit>(std::move(exitCond)), std::move(updateTable)));
    }
    if (postamble) {
        appendStmt(res, std::move(postamble));
    }
    if (res) return res;

    assert(false && "Not Implemented");
    return nullptr;
}

/** generate RAM code for recursive relations in a strongly-connected component */
std::unique_ptr<RamStatement> AstTranslator::translateUpdateRecursiveRelation(
        const std::set<const AstRelation*>& scc, const RecursiveClauses* recursiveClauses, int indexOfScc) {
    // initialize sections
    std::unique_ptr<RamStatement> preamble;
    std::unique_ptr<RamSequence> clearTable(new RamSequence());
    std::unique_ptr<RamSequence> updateTable(new RamSequence());
    std::unique_ptr<RamStatement> postamble;

    // --- create preamble ---

    // mappings for temporary relations
    std::map<const AstRelation*, std::unique_ptr<RamRelationReference>> rrel;
    std::map<const AstRelation*, std::unique_ptr<RamRelationReference>> relDelta;
    std::map<const AstRelation*, std::unique_ptr<RamRelationReference>> relNew;

    // utility to convert a list of AstConstraints to a disjunction
    auto toAstDisjunction = [&](std::vector<AstConstraint*> constraints) -> std::unique_ptr<AstConstraint> {
        std::unique_ptr<AstConstraint> result;
        for (const auto& cur : constraints) {
            if (result == nullptr) {
                result = std::unique_ptr<AstConstraint>(cur->clone());
            } else {
                result = std::make_unique<AstDisjunctionConstraint>(std::move(result), std::unique_ptr<AstConstraint>(cur->clone()));
            }
        }
        return result;
    };

    /* Compute non-recursive clauses for relations in scc and push
       the results in their delta tables. */
    for (const AstRelation* rel : scc) {

        std::unique_ptr<RamStatement> updateRelTable;
        std::unique_ptr<RamStatement> clearRelTable;

        /* create two temporary tables for relaxed semi-naive evaluation */
        rrel[rel] = translateRelation(rel);
        relDelta[rel] = translateDeltaRelation(rel);
        relNew[rel] = translateNewRelation(rel);

        /* create update statements for fixpoint (even iteration) */
        if (!Global::config().has("incremental")) {
            appendStmt(updateRelTable,
                    std::make_unique<RamSequence>(
                            std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(rrel[rel]->clone()),
                                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone())),
                            std::make_unique<RamSwap>(
                                    std::unique_ptr<RamRelationReference>(relDelta[rel]->clone()),
                                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone())),
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone()))));

        } else {
            appendStmt(clearRelTable,
                    std::make_unique<RamSequence>(
                            // create updated_plus and updated_minus relations
                            std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateUpdatedMinusRelation(rel)->clone())),
                            std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateUpdatedPlusRelation(rel)->clone())),

                            /*
                            std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDeltaDiffMinusRelation(rel)->clone())),
                            std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDeltaDiffPlusRelation(rel)->clone())),
                            */

                            std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDeltaRelation(rel)->clone())),
                            std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone()))
                            ));

            appendStmt(updateRelTable,
                    std::make_unique<RamSequence>(
                            // populate the diff minus relations
                            // merge new_diff_minus into diff_minus to update with new tuples from current iteration
                            std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())),

                            // update the diff plus relations
                            // merge new_diff_plus into diff_plus to update with new tuples from current iteration
                            std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())),

                            // update the diff applied relations
                            // assume diff_applied contains all correct tuples from previous epoch
                            // merge new_diff_minus and new_diff_plus into diff_plus_applied to update with new tuples from current iteration
                            // order is important - minus should be applied before plus,
                            // as plus may be able to update tuples that are deleted in the current epoch
                            std::make_unique<RamMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())),
                            std::make_unique<RamMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())),

                            /*
                            std::make_unique<RamDeltaMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDeltaDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateRelation(rel)->clone())),

                            std::make_unique<RamDeltaMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDeltaDiffPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone())),

                            std::make_unique<RamDeltaMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDeltaRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateRelation(rel)->clone())),

                            std::make_unique<RamDeltaMerge>(
                                    std::unique_ptr<RamRelationReference>(translateDeltaDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone())),
                                    */

                            std::make_unique<RamSemiMerge>(
                                    std::unique_ptr<RamRelationReference>(translateActualDiffPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateUpdatedPlusRelation(rel)->clone()),
                                    true),

                            std::make_unique<RamSemiMerge>(
                                    std::unique_ptr<RamRelationReference>(translateActualDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateUpdatedMinusRelation(rel)->clone()),
                                    true)

                            /*
                            std::make_unique<RamUpdateMerge>(
                                    std::unique_ptr<RamRelationReference>(translateUpdatedMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone())),

                            std::make_unique<RamUpdateMerge>(
                                    std::unique_ptr<RamRelationReference>(translateUpdatedPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone()),
                                    std::unique_ptr<RamRelationReference>(translateRelation(rel)->clone()))
                                    */

                            ));
        }

        /* measure update time for each relation */
        if (Global::config().has("profile")) {
            updateRelTable = std::make_unique<RamLogRelationTimer>(std::move(updateRelTable),
                    LogStatement::cRecursiveRelation(toString(rel->getName()), rel->getSrcLoc()),
                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone()));
        }


        if (Global::config().has("incremental")) {
            appendStmt(postamble, std::make_unique<RamSequence>(
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())),
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone()))));
        } else {
            /* drop temporary tables after recursion */
            appendStmt(postamble, std::make_unique<RamSequence>(
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(relDelta[rel]->clone())),
                                          std::make_unique<RamDrop>(
                                                  std::unique_ptr<RamRelationReference>(relNew[rel]->clone()))));
        }


        /* Generate code for non-recursive part of relation */
        appendStmt(preamble, translateUpdateNonRecursiveRelation(*rel, recursiveClauses));

        if (Global::config().has("incremental")) {
            // update the diff applied relations
            // merge the full relation into diff_applied
            // merge new_diff_minus and new_diff_plus into diff_plus_applied to update with new tuples from current iteration
            // order is important - minus should be applied before plus,
            // as plus may be able to update tuples that are deleted in the current epoch
            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone())));
            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone())));
            appendStmt(preamble,
                    std::make_unique<RamSemiMerge>(
                            std::unique_ptr<RamRelationReference>(translateActualDiffPlusRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateUpdatedPlusRelation(rel)->clone())
                            ));
            appendStmt(preamble,
                    std::make_unique<RamSemiMerge>(
                            std::unique_ptr<RamRelationReference>(translateActualDiffMinusRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(rel)->clone()),
                            std::unique_ptr<RamRelationReference>(translateUpdatedMinusRelation(rel)->clone())
                            ));
        } else {
            /* Generate merge operation for temp tables */
            appendStmt(preamble,
                    std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(relDelta[rel]->clone()),
                        std::unique_ptr<RamRelationReference>(rrel[rel]->clone())));
        }

        /* Add update operations of relations to parallel statements */
        updateTable->add(std::move(updateRelTable));
        clearTable->add(std::move(clearRelTable));
    }

    // for incremental, create a temporary table storing the max iteration number in the current SCC
    // we want the relation to have a single fact, like
    // @max_iter_scc_i(
    //   max(
    //     max @iter : rel_1(_, _, @iter, _, _), 
    //     max @iter : rel_2(_, _, @iter, _, _),
    //     ...)).
    auto maxIterRelation = new RamRelation("scc_" + std::to_string(indexOfScc) + "_@max_iter", 1, 1, std::vector<std::string>({"max_iter"}), std::vector<std::string>({"s"}), RelationRepresentation::DEFAULT);
    auto maxIterRelationRef = std::make_unique<RamRelationReference>(maxIterRelation);

    if (Global::config().has("incremental")) {
        // appendStmt(preamble, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(maxIterRelationRef->clone())));

        // we make the final project first
        std::vector<std::unique_ptr<RamExpression>> maxIterNumbers;
        int ident = 0;
        for (const AstRelation* rel : scc) {
            maxIterNumbers.push_back(std::make_unique<RamTupleElement>(ident, 0));
            ident++;
        }
        auto maxIterNumber = std::make_unique<RamIntrinsicOperator>(FunctorOp::MAX, std::move(maxIterNumbers));

        // create a set of aggregates over the relations in the scc
        // a RamAggregate is a nested structure
        std::vector<std::unique_ptr<RamExpression>> maxIterNumFunctor;
        maxIterNumFunctor.push_back(std::move(maxIterNumber));
        std::unique_ptr<RamOperation> outerMaxIterAggregate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(maxIterRelationRef->clone()), std::move(maxIterNumFunctor));

        ident = 0;
        for (const AstRelation* rel : scc) {
            outerMaxIterAggregate = std::make_unique<RamAggregate>(std::move(outerMaxIterAggregate), AggregateFunction::MAX, std::unique_ptr<RamRelationReference>(rrel[rel]->clone()), std::make_unique<RamTupleElement>(ident, rrel[rel]->get()->getArity() - 2), std::make_unique<RamTrue>(), ident);
            ident++;
        }

        appendStmt(preamble, std::make_unique<RamQuery>(std::move(outerMaxIterAggregate)));
    }

    // --- build main loop ---

    std::unique_ptr<RamParallel> loopSeq(new RamParallel());

    // create a utility to check SCC membership
    auto isInSameSCC = [&](const AstRelation* rel) {
        return std::find(scc.begin(), scc.end(), rel) != scc.end();
    };

    // a mapper to name unnamed variables
    struct UnnamedVariableRenamer : public AstNodeMapper {
        mutable int counter = 0;

        UnnamedVariableRenamer() = default;

        std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
            // apply recursive
            node->apply(*this);

            // replace unknown variables
            if (dynamic_cast<AstUnnamedVariable*>(node.get())) {
                auto name = " _unnamed_negation_var" + toString(++counter);
                return std::make_unique<AstVariable>(name);
            }

            // otherwise nothing
            return node;
        }
    };

    /* Compute temp for the current tables */
    for (const AstRelation* rel : scc) {
        std::unique_ptr<RamStatement> loopRelSeq;

        std::set<AstRelationIdentifier> processedRestrictionAtoms;
        std::set<AstRelationIdentifier> processedRestrictionCreates;
        std::set<AstRelationIdentifier> processedRestrictionDeletions;

        /* Find clauses for relation rel */
        for (size_t i = 0; i < rel->clauseSize(); i++) {
            AstClause* cl = rel->getClause(i);

            // skip non-recursive clauses
            if (!recursiveClauses->recursive(cl)) {
                continue;
            }

            // each recursive rule results in several operations
            const auto& atoms = cl->getAtoms();
            const auto& negations = cl->getNegations();

            int version = 0;
            int diffVersion = 1;
            if (Global::config().has("incremental")) {
                // store previous count and current count to determine if the rule is insertion or deletion
                // auto prevCount = cl->getHead()->getArgument(rel->getArity() - 2);
                auto curCount = cl->getHead()->getArgument(rel->getArity() - 1);

                // these should not be nullptrs
                // auto prevCountNum = dynamic_cast<AstNumberConstant*>(prevCount);
                auto curCountNum = dynamic_cast<AstNumberConstant*>(curCount);

                if (/*prevCountNum == nullptr ||*/ curCountNum == nullptr) {
                    std::cerr << "count annotations are not intialized!" << std::endl;
                }

                nameUnnamedVariables(cl);

                // check if this clause is re-inserting hidden tuples
                // bool isReinsertionRule = (*prevCountNum == AstNumberConstant(1) && *curCountNum == AstNumberConstant(1));
                bool isReinsertionRule = *curCountNum == AstNumberConstant(2);
                bool isRedeletionRule = *curCountNum == AstNumberConstant(-2);
                bool isInsertionRule = (*curCountNum == AstNumberConstant(1)) && !isReinsertionRule;
                bool isDeletionRule = (*curCountNum == AstNumberConstant(-1));

                if (isReinsertionRule) {
                    std::unique_ptr<AstClause> rdiff(cl->clone());

                    rdiff->getHead()->setName(translateNewDiffPlusRelation(rel)->get()->getName());

                    // this is needed because the count is set to 2 by IncrementalTransformer, so it is detected and reset here
                    rdiff->getHead()->setArgument(rel->getArity() - 1, std::make_unique<AstNumberConstant>(1));

                    for (size_t k = 0; k < atoms.size(); k++) {
                        if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                        } else {
                            // for differential, create an existence check on the previous epoch's relation
                            auto noPrevDelta = rdiff->getAtoms()[k]->clone();
                            noPrevDelta->setArgument(noPrevDelta->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            noPrevDelta->setArgument(noPrevDelta->getArity() - 2, std::make_unique<AstNumberConstant>(-1));
                            rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevDelta)));
                        }

                        // ensure body tuples all come from diff_applied
                        rdiff->getAtoms()[k]->setName(translateDiffAppliedRelation(getAtomRelation(rdiff->getAtoms()[k], program))->get()->getName());
                    }

                    // for incremental, we use iteration counts to simulate delta relation rather than explicitly having a separate relation
                    auto diffAppliedHeadAtom = cl->getHead()->clone();
                    diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                    // the 2 indicates that it's a re-insertion, which is processed in the Synthesiser to generate a correct non-existence constraint
                    diffAppliedHeadAtom->setArgument(rel->getArity() - 1, std::make_unique<AstNumberConstant>(1));

                    // add constraints saying that each body tuple must have existed in the previous epoch
                    std::vector<AstConstraint*> existsReinsertion;

                    // diffVersion = atoms.size() + negations.size() + 1 so it doesn't conflict with any other rules (in particular rules with negation)
                    diffVersion = atoms.size() + negations.size() + 1;
                    /*
                    for (size_t i = 0; i < atoms.size(); i++) {
                        // ensure tuple actually existed
                        auto curAtom = atoms[i]->clone();
                        curAtom->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());

                        // curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                        // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());

                        rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(curAtom)));
                    }
                    */

                    // if we have incremental evaluation, we use iteration counts to simulate delta relations
                    // rather than explicitly having a separate relation
                    rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                            std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                    /*
                    // a tuple should only be reinserted if that tuple is deleted
                    auto deletedTuple = cl->getHead()->clone();
                    // deletedTuple->setName(translateDiffMinusCountRelation(rel)->get()->getName());
                    deletedTuple->setName(translateDiffMinusRelation(rel)->get()->getName());
                    deletedTuple->setArgument(deletedTuple->getArity() - 1, std::make_unique<AstVariable>("@deleted_count"));
                    deletedTuple->setArgument(deletedTuple->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                    // deletedTuple->setArgument(deletedTuple->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                    rdiff->addToBody(std::unique_ptr<AstAtom>(deletedTuple));
                    rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE, std::make_unique<AstVariable>("@deleted_count"), std::make_unique<AstNumberConstant>(0)));
                    */

                    std::vector<std::unique_ptr<AstLiteral>> notDeletedChecks;

                    // process negations
                    for (size_t j = 0; j < negations.size(); j++) {
                        // each negation needs to have either not existed, or be deleted
                        // for the non-existence case, we use a positive negation instead
                        auto negatedAtom = negations[j]->getAtom()->clone();
                        negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));

                        // negations shouldn't exist in diff_minus_count, otherwise they will be processed by insertion rules
                        auto notDeleted = negations[j]->getAtom()->clone();
                        // notDeleted->setName(translateDiffMinusCountRelation(getAtomRelation(notDeleted, program))->get()->getName());
                        notDeleted->setName(translateDiffMinusRelation(getAtomRelation(notDeleted, program))->get()->getName());
                        notDeleted->setArgument(notDeleted->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                        // notDeleted->setArgument(notDeleted->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                        // notDeleted->setArgument(notDeleted->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                        notDeletedChecks.push_back(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(notDeleted)));
                    }

                    rdiff->clearNegations();

                    for (auto& notDeleted : notDeletedChecks) {
                        rdiff->addToBody(std::move(notDeleted));
                    }

                    version = 0;
                    // use delta versions of relations for semi-naive evaluation
                    for (size_t j = 0; j < atoms.size(); j++) {
                        if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                            continue;
                        }


                        // create clone
                        std::unique_ptr<AstClause> r1(rdiff->clone());

                        // set the j-th atom to use DeltaDiffApplied
                        // r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        r1->getAtoms()[j]->setName(translateUpdatedMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        /*
                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                    std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    */

                        // any atoms before atom j should be in earlier iterations, check this by a constraint on the iteration number
                        for (size_t k = 0; k < j; k++) {
                            if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                            }
                        }


                        // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                        for (size_t k = j + 1; k < atoms.size(); k++) {
                            if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                            }
                        }

                        /*
                        // for the reinsertion rule, we only want to process tuples that are deleted from earlier iterations
                        auto deletedAtom = atoms[j]->clone();
                        deletedAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        deletedAtom->setArgument(deletedAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-2));
                        // deletedAtom->setArgument(deletedAtom->getArity() - 1, std::make_unique<AstVariable>("@prev_count"));
                        // deletedAtom->setArgument(deletedAtom->getArity() - 2, std::make_unique<AstVariable>("@prev_iteration"));
                        r1->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(deletedAtom)));

                        auto noDeletionPrior = atoms[j]->clone();
                        noDeletionPrior->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        noDeletionPrior->setArgument(noDeletionPrior->getArity() - 1, std::make_unique<AstNumberConstant>(-2));
                        noDeletionPrior->setArgument(noDeletionPrior->getArity() - 2, std::make_unique<AstVariable>("@prev_iteration"));
                        r1->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noDeletionPrior)));
                        */
                        for (size_t k = 0; k < atoms.size(); k++) {
                            if (k != j) {
                                if (isInSameSCC(getAtomRelation(atoms[k], program))){
                                    // for differential, create an existence check on the previous epoch's relation
                                    auto noPrevDelta = atoms[k]->clone();
                                    noPrevDelta->setArgument(noPrevDelta->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                    noPrevDelta->setArgument(noPrevDelta->getArity() - 2, std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1)));
                                    r1->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevDelta)));
                                }

                                auto noPrior = atoms[k]->clone();
                                noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[k], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                r1->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                            }
                        }

                        /*
                        // add a constraint that the deleted atom was not in delta
                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT, std::make_unique<AstVariable>("@prev_iteration"), std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                        */

                        std::cout << "reinsertion recursive: " << *r1 << std::endl;

                        AstExecutionPlan* plan;
                        if (r1->getExecutionPlan() != nullptr) {
                            plan = r1->getExecutionPlan()->clone();
                        } else {
                            plan = new AstExecutionPlan();
                        }

                        plan->setOrderFor(version, diffVersion, std::move(createReordering(*r1, j + 1, version, diffVersion)));
                        r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

                        // translate rdiff
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel->getName());
                            const SrcLocation& srcLocation = r1->getSrcLoc();
                            const std::string clText = stringify(toString(*r1));
                            const std::string logTimerStatement =
                                    LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*r1) << "\nin file ";
                        ds << r1->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(loopRelSeq, std::move(rule));

                        version++;
                    }
                } else if (isRedeletionRule) {
                    std::unique_ptr<AstClause> rdiff(cl->clone());

                    rdiff->getHead()->setName(translateNewDiffMinusRelation(rel)->get()->getName());

                    // this is needed because the count is set to 2 by IncrementalTransformer, so it is detected and reset here
                    rdiff->getHead()->setArgument(rel->getArity() - 1, std::make_unique<AstNumberConstant>(-1));

                    for (size_t k = 0; k < atoms.size(); k++) {
                        if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                        } else {
                            // for differential, create an existence check on the previous epoch's relation
                            auto noPrevDelta = rdiff->getAtoms()[k]->clone();
                            noPrevDelta->setArgument(noPrevDelta->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            noPrevDelta->setArgument(noPrevDelta->getArity() - 2, std::make_unique<AstNumberConstant>(-1));
                            noPrevDelta->setName(translateDiffAppliedRelation(getAtomRelation(noPrevDelta, program))->get()->getName());
                            rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevDelta)));
                        }

                        // ensure body tuples all come from diff_applied
                        // rdiff->getAtoms()[k]->setName(translateDiffAppliedRelation(getAtomRelation(rdiff->getAtoms()[k], program))->get()->getName());
                    }

                    // for incremental, we use iteration counts to simulate delta relation rather than explicitly having a separate relation
                    auto diffAppliedHeadAtom = cl->getHead()->clone();
                    diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                    // the 2 indicates that it's a re-insertion, which is processed in the Synthesiser to generate a correct non-existence constraint
                    diffAppliedHeadAtom->setArgument(rel->getArity() - 1, std::make_unique<AstNumberConstant>(-1));

                    // add constraints saying that each body tuple must have existed in the previous epoch
                    std::vector<AstConstraint*> existsReinsertion;

                    // diffVersion = atoms.size() + negations.size() + 1 so it doesn't conflict with any other rules (in particular rules with negation)
                    diffVersion = atoms.size() + negations.size() + 1;
                    /*
                    for (size_t i = 0; i < atoms.size(); i++) {
                        // ensure tuple actually existed
                        auto curAtom = atoms[i]->clone();
                        curAtom->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());

                        // curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                        curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                        // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());

                        rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(curAtom)));
                    }
                    */

                    // if we have incremental evaluation, we use iteration counts to simulate delta relations
                    // rather than explicitly having a separate relation
                    rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                            std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                    /*
                    // a tuple should only be reinserted if that tuple is deleted
                    auto deletedTuple = cl->getHead()->clone();
                    // deletedTuple->setName(translateDiffMinusCountRelation(rel)->get()->getName());
                    deletedTuple->setName(translateDiffMinusRelation(rel)->get()->getName());
                    deletedTuple->setArgument(deletedTuple->getArity() - 1, std::make_unique<AstVariable>("@deleted_count"));
                    deletedTuple->setArgument(deletedTuple->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                    // deletedTuple->setArgument(deletedTuple->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                    rdiff->addToBody(std::unique_ptr<AstAtom>(deletedTuple));
                    rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE, std::make_unique<AstVariable>("@deleted_count"), std::make_unique<AstNumberConstant>(0)));
                    */

                    std::vector<std::unique_ptr<AstLiteral>> notDeletedChecks;

                    // process negations
                    for (size_t j = 0; j < negations.size(); j++) {
                        // each negation needs to have either not existed, or be deleted
                        // for the non-existence case, we use a positive negation instead
                        auto negatedAtom = negations[j]->getAtom()->clone();
                        negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                        rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));

                        // negations shouldn't exist in diff_minus_count, otherwise they will be processed by insertion rules
                        auto notDeleted = negations[j]->getAtom()->clone();
                        // notDeleted->setName(translateDiffMinusCountRelation(getAtomRelation(notDeleted, program))->get()->getName());
                        notDeleted->setName(translateDiffMinusRelation(getAtomRelation(notDeleted, program))->get()->getName());
                        notDeleted->setArgument(notDeleted->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                        // notDeleted->setArgument(notDeleted->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                        // notDeleted->setArgument(notDeleted->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                        notDeletedChecks.push_back(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(notDeleted)));
                    }

                    rdiff->clearNegations();

                    for (auto& notDeleted : notDeletedChecks) {
                        rdiff->addToBody(std::move(notDeleted));
                    }

                    version = 0;
                    // use delta versions of relations for semi-naive evaluation
                    for (size_t j = 0; j < atoms.size(); j++) {
                        if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                            continue;
                        }


                        // create clone
                        std::unique_ptr<AstClause> r1(rdiff->clone());

                        // set the j-th atom to use DeltaDiffApplied
                        // r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        r1->getAtoms()[j]->setName(translateUpdatedPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        /*
                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                    std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    */

                        // any atoms before atom j should be in earlier iterations, check this by a constraint on the iteration number
                        for (size_t k = 0; k < j; k++) {
                            if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                            }
                        }


                        // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                        for (size_t k = j + 1; k < atoms.size(); k++) {
                            if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                            }
                        }

                        /*
                        // for the reinsertion rule, we only want to process tuples that are inserted from earlier iterations
                        auto insertedAtom = atoms[j]->clone();
                        insertedAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        insertedAtom->setArgument(insertedAtom->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                        // insertedAtom->setArgument(insertedAtom->getArity() - 1, std::make_unique<AstVariable>("@prev_count"));
                        // insertedAtom->setArgument(insertedAtom->getArity() - 2, std::make_unique<AstVariable>("@prev_iteration"));
                        r1->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(insertedAtom)));

                        auto noInsertionPrior = atoms[j]->clone();
                        noInsertionPrior->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                        noInsertionPrior->setArgument(noInsertionPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                        noInsertionPrior->setArgument(noInsertionPrior->getArity() - 2, std::make_unique<AstVariable>("@prev_iteration"));
                        r1->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noInsertionPrior)));
                        */

                        for (size_t k = 0; k < atoms.size(); k++) {
                            if (k != j) {
                                if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                    // for differential, create an existence check on the previous epoch's relation
                                    auto noPrevDelta = atoms[k]->clone();
                                    noPrevDelta->setArgument(noPrevDelta->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                    noPrevDelta->setArgument(noPrevDelta->getArity() - 2, std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1)));
                                    noPrevDelta->setName(translateDiffAppliedRelation(getAtomRelation(noPrevDelta, program))->get()->getName());
                                    r1->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevDelta)));
                                }

                                auto noPrior = atoms[k]->clone();
                                // noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                r1->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));

                            }
                        }

                        /*
                        // add a constraint that the inserted atom was not in delta
                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT, std::make_unique<AstVariable>("@prev_iteration"), std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                        */

                        /*
                        // do a sips-based reordering
                        // generate a list of variables that are a-priori bound by the head atom
                        std::set<std::string> boundVariables;
                        for (size_t k = 0; k < rel->getArity(); k++) {
                            auto arg = r1->getHead()->getArgument(k);
                            if (auto var = dynamic_cast<AstVariable*>(arg)) {
                                boundVariables.insert("+" + toString(*var));
                            }
                        }

                        // and also by the iteration number for the delta relation
                        boundVariables.insert(toString(*(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2))));

                        // get existing execution plan
                        AstExecutionPlan* plan;
                        if (r1->getExecutionPlan() != nullptr) {
                            plan = r1->getExecutionPlan()->clone();
                        } else {
                            plan = new AstExecutionPlan();
                        }

                        std::unique_ptr<AstExecutionOrder> executionReordering;
                        if (plan->hasOrderFor(version, diffVersion)) {
                            executionReordering = std::unique_ptr<AstExecutionOrder>(plan->getOrderFor(version, diffVersion).clone());
                        } else {
                            AstExecutionOrder* existingOrder;

                            if (plan->hasOrderFor(version, 0)) {
                                existingOrder = plan->getOrderFor(version, 0).clone();
                            } else {
                                existingOrder = new AstExecutionOrder();
                                for (size_t k = 1; k <= atoms.size(); k++) {
                                    existingOrder->appendAtomIndex(k);
                                }
                            }

                            // create a clone of cl for reordering purposes
                            auto reorderedClause = std::unique_ptr<AstClause>(cl->clone());

                            std::vector<unsigned int> newOrderVector(existingOrder->size());
                            std::transform(existingOrder->begin(), existingOrder->end(), newOrderVector.begin(),
                                    [](unsigned int i) -> unsigned int { return i - 1; });

                            reorderedClause->reorderAtoms(newOrderVector);

                            // create a sips function and do reordering
                            auto sipsFunc = ReorderLiteralsTransformer::getSipsFunction("incremental-reordering-rediscovery");
                            // auto sipsFunc = ReorderLiteralsTransformer::getSipsFunction("none");
                            auto reordering = ReorderLiteralsTransformer::applySips(sipsFunc, reorderedClause->getAtoms(), boundVariables);

                            // put this into an AstExecutionOrder
                            executionReordering = std::make_unique<AstExecutionOrder>();
                            for (auto i : reordering) {
                                executionReordering->appendAtomIndex((*existingOrder)[i]);
                            }
                        }
                        */

                        /*
                        // create another clone for filter creation purposes
                        auto filterClause = std::unique_ptr<AstClause>(cl->clone());
                        plan->setOrderFor(version, diffVersion, std::unique_ptr<AstExecutionOrder>(executionReordering->clone()));
                        filterClause->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan->clone()));
                        */

                        /*
                        auto restrictionAtoms = createIncrementalRediscoverFilters(*cl, i, executionReordering->getOrder(), *program, recursiveClauses);

                        // add RamCreate statements for each restriction relation
                        // this has to go before adding the rules populating them so that the relations exist at that point
                        for (AstRelation* restrictionRel : restrictionAtoms.first) {
                            if (!contains(processedRestrictionCreates, restrictionRel->getName())) {
                                // if not already processed
                                appendStmt(preamble, 
                                        std::make_unique<RamCreate>(
                                            std::unique_ptr<RamRelationReference>(translateRelation(restrictionRel)->clone())));

                                processedRestrictionCreates.insert(restrictionRel->getName());
                            }
                        }

                        // create a 'rule' in preamble that populates this restriction filter
                        for (AstAtom* restrictionAtom : restrictionAtoms.second) {
                            // restriction atoms are uniquely identified by the atom name
                            if (!contains(processedRestrictionAtoms, restrictionAtom->getName())) {
                                // create an AstClause for the preamble
                                auto restrictionClause = std::make_unique<AstClause>();

                                restrictionClause->setHead(std::unique_ptr<AstAtom>(restrictionAtom->clone()));

                                auto relationHead = cl->getHead()->clone();
                                relationHead->setName(translateDiffMinusRelation(rel)->get()->getName());
                                relationHead->setArgument(rel->getArity() - 1, std::make_unique<AstUnnamedVariable>());

                                // remove all irrelevant arguments
                                for (size_t k = 0; k < relationHead->argSize(); k++) {
                                    if (dynamic_cast<AstVariable*>(relationHead->getArgument(k)) == nullptr) {
                                        relationHead->setArgument(k, std::make_unique<AstUnnamedVariable>());
                                    }
                                }

                                restrictionClause->addToBody(std::unique_ptr<AstAtom>(relationHead));

                                appendStmt(preamble, ClauseTranslator(*this).translateClause(*restrictionClause, *restrictionClause));

                                // create an AstClause for updateTable
                                auto restrictionUpdateClause = std::make_unique<AstClause>();

                                restrictionUpdateClause->setHead(std::unique_ptr<AstAtom>(restrictionAtom->clone()));

                                auto relationUpdateHead = cl->getHead()->clone();
                                relationUpdateHead->setName(translateNewDiffMinusRelation(rel)->get()->getName());
                                relationUpdateHead->setArgument(rel->getArity() - 1, std::make_unique<AstUnnamedVariable>());

                                // remove all irrelevant arguments
                                for (size_t k = 0; k < relationUpdateHead->argSize(); k++) {
                                    if (dynamic_cast<AstVariable*>(relationUpdateHead->getArgument(k)) == nullptr) {
                                        relationUpdateHead->setArgument(k, std::make_unique<AstUnnamedVariable>());
                                    }
                                }

                                restrictionUpdateClause->addToBody(std::unique_ptr<AstAtom>(relationUpdateHead));

                                updateTable->add(ClauseTranslator(*this).translateClause(*restrictionUpdateClause, *restrictionUpdateClause));

                                processedRestrictionAtoms.insert(restrictionAtom->getName());
                            }

                            // also add the restriction atom to the body of the rule
                            r1->addToBody(std::unique_ptr<AstAtom>(restrictionAtom->clone()));
                        }

                        // drop the restriction relations after the loop
                        for (AstRelation* restrictionRel : restrictionAtoms.first) {
                            if (!contains(processedRestrictionDeletions, restrictionRel->getName())) {
                                // drop the filter relation at the end of the loop
                                appendStmt(postamble, 
                                        std::make_unique<RamDrop>(
                                            std::unique_ptr<RamRelationReference>(translateRelation(restrictionRel)->clone())));

                                processedRestrictionDeletions.insert(restrictionRel->getName());
                            }
                        }


                        // set an execution plan so the diff_plus version of the relation is evaluated first
                        // get existing execution plan - we are guaranteed to have a plan because of the sips reordering
                        AstExecutionOrder* currentOrder = executionReordering->clone();

                        AstExecutionOrder* order = new AstExecutionOrder();

                        // for each atom in the order, check which filter atom should go before it
                        int filterAtomIndex = 0;
                        
                        for (size_t k = 0; k < currentOrder->size(); k++) {
                            int atomIndex = (*currentOrder)[k];
                            bool covers = true;

                            if (filterAtomIndex >= restrictionAtoms.second.size()) {
                                covers = false;
                            }

                            // if atomIndex refers to a filter atom, it doesn't cover anything
                            if (atomIndex > cl->getAtoms().size()) {
                                covers = false;
                            }

                            if (covers) {
                                // check if the current filterAtom covers this
                                for (AstArgument* filterArg : restrictionAtoms.second[filterAtomIndex]->getArguments()) {
                                    bool found = false;
                                    for (AstArgument* bodyArg : r1->getAtoms()[atomIndex - 1]->getArguments()) {
                                        if (*bodyArg == *filterArg) {
                                            found = true;
                                            break;
                                        }
                                    }
                                    
                                    if (!found) {
                                        covers = false;
                                        break;
                                    }
                                }
                            }

                            // we know this filter atom covers the body atom, so we insert it into the order
                            if (covers) {
                                if (contains(currentOrder->getOrder(), atoms.size() + filterAtomIndex + 1)) {
                                    // check if the corresponding filter atom is already in the order
                                    order->appendAtomIndex(atomIndex);
                                } else if (k == 0) {
                                    // only the first filter should come before the atom, the subsequent ones should go after to prevent cross products
                                    order->appendAtomIndex(atoms.size() + filterAtomIndex + 1);
                                    order->appendAtomIndex(atomIndex);
                                } else {
                                    order->appendAtomIndex(atomIndex);
                                    order->appendAtomIndex(atoms.size() + filterAtomIndex + 1);
                                }
                                filterAtomIndex++;
                            } else {
                                order->appendAtomIndex(atomIndex);
                            }
                        }

                        // if (!plan->hasOrderFor(version, diffVersion)) {
                        plan->setOrderFor(version, diffVersion, std::unique_ptr<AstExecutionOrder>(order));
                        // }
                        r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan->clone()));
                        */


                        std::cout << "redeletion recursive: " << *r1 << std::endl;

                        AstExecutionPlan* plan;
                        if (r1->getExecutionPlan() != nullptr) {
                            plan = r1->getExecutionPlan()->clone();
                        } else {
                            plan = new AstExecutionPlan();
                        }

                        plan->setOrderFor(version, diffVersion, std::move(createReordering(*r1, j + 1, version, diffVersion)));
                        r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

                        // translate rdiff
                        std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                        // add logging
                        if (Global::config().has("profile")) {
                            const std::string& relationName = toString(rel->getName());
                            const SrcLocation& srcLocation = r1->getSrcLoc();
                            const std::string clText = stringify(toString(*r1));
                            const std::string logTimerStatement =
                                    LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                            const std::string logSizeStatement =
                                    LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                            rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                    logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())));
                        }

                        // add debug info
                        std::ostringstream ds;
                        ds << toString(*r1) << "\nin file ";
                        ds << r1->getSrcLoc();
                        rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                        // add rule to result
                        appendStmt(loopRelSeq, std::move(rule));

                        version++;
                    }
                } else {
                    // AstAtom* atom = atoms[j];
                    // const AstRelation* atomRelation = getAtomRelation(atom, program);

                    // clone the clause so we can use diff and diff_applied auxiliary relations
                    // std::unique_ptr<AstClause> rdiff(cl->clone());

                    if (isInsertionRule) {
                        diffVersion = 1;
                        for (size_t i = 0; i < atoms.size(); i++) {
                            // an insertion rule should look as follows:
                            // R :- R_1, R_2, ..., diff_plus_count_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            std::unique_ptr<AstClause> rdiff(cl->clone());

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffPlusRelation(rel)->get()->getName());

                            /*
                            // ensure i-th tuple did not exist previously, this prevents double insertions
                            auto noPrevious = atoms[i]->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                            */

                            // the current version of the rule should have diff_plus_count in the i-th position
                            // rdiff->getAtoms()[i]->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            rdiff->getAtoms()[i]->setName(translateActualDiffPlusRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            /*
                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));
                                        */

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious)));
                            }

                            for (size_t j = i + 1; j < atoms.size(); j++) {
                                rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            }

                            for (size_t j = 0; j < atoms.size(); j++) {
                                // add a constraint saying that the tuples must have existed previously
                                rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                            std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                            std::make_unique<AstNumberConstant>(0)));

                                // add a constraint saying that the delta tuple can't have existed previously
                                auto noPrior = atoms[j]->clone();
                                noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_plus
                            rdiff->getHead()->setName(translateNewDiffPlusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // add a constraint saying that tuple j should be in the previous iteration, simulating delta relations
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                /*
                                if (j == i) {
                                    r1->getAtoms()[j]->setName(translateDeltaDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                } else {
                                    r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                }
                                */

                                // any atoms before atom j should be in earlier itereations, check this by a constraint on the iteration number
                                for (size_t k = 0; k < j; k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // set an execution plan so the diff_plus version of the relation is evaluated first
                                // get existing execution plan
                                AstExecutionPlan* plan;
                                if (r1->getExecutionPlan() != nullptr) {
                                    plan = r1->getExecutionPlan()->clone();
                                } else {
                                    plan = new AstExecutionPlan();
                                }

                                plan->setOrderFor(version, diffVersion, std::move(createReordering(*r1, diffVersion, version, diffVersion)));
                                r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

                                // std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }
                            diffVersion++;
                        }

                        diffVersion = atoms.size() + 1;
                        // TODO: this doesn't work when there are functors in the negation because the constraint checking for equality isn't generated :(
                        // i.e., if there is (i-1) inside the negation, when we convert this to a diff_plus, usually there would be a constraint _tmp_0 = i-1,
                        // but this doesn't happen for negations
                        for (size_t i = 0; i < negations.size(); i++) {
                            // an insertion rule should look as follows:
                            // R :- R_1, R_2, ..., diff_plus_count_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            auto rdiff = cl->clone();

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffPlusRelation(rel)->get()->getName());

                            // clone the i-th negation's atom
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            auto negatedAtomNamed = negations[i]->getAtom()->clone();
                            /*
                            UnnamedVariableRenamer renamer;
                            negatedAtomNamed->apply(renamer);
                            */

                            auto negatedAtom = negatedAtomNamed->clone();

                            // negatedAtom->setName(translateDiffMinusCountRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            negatedAtom->setName(translateActualDiffMinusRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            // negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                            negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstVariable>("@negation_count"));
                            // negatedAtom->setArgument(negatedAtom->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                            negatedAtom->setArgument(negatedAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                            rdiff->addToBody(std::unique_ptr<AstAtom>(negatedAtom));

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                        std::make_unique<AstVariable>("@negation_count"),
                                        std::make_unique<AstNumberConstant>(0)));

                            /*
                            auto noPrevious = negatedAtomNamed->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(noPrevious, program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                            */

                            // atoms before the i-th position should not fulfill the conditions for incremental deletion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = negations[j]->getAtom()->clone();
                                // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(curAtom, program))->get()->getName());
                                curAtom->setName(translateDiffMinusRelation(getAtomRelation(curAtom, program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                                // also ensure tuple existed previously
                                auto noPrevious = negations[j]->getAtom()->clone();
                                noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(noPrevious, program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                AstAtom* negatedAtom;
                                /*
                                if (j == i) {
                                    negatedAtom = negatedAtomNamed->clone();
                                } else {
                                */
                                    negatedAtom = negations[j]->getAtom()->clone();
                                // }
                                negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            // the base relation for addition should be diff_applied, so translate each positive atom to the diff applied version
                            for (size_t j = 0; j < atoms.size(); j++) {
                                rdiff->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious)));

                                // add a constraint saying that the tuples must have existed previously
                                rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                            std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                            std::make_unique<AstNumberConstant>(0)));

                                // add a constraint saying that the delta tuple can't have existed previously
                                auto noPrior = atoms[j]->clone();
                                noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_plus
                            rdiff->getHead()->setName(translateNewDiffPlusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // r1->getAtoms()[j]->setName(translateDeltaDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->getAtoms()[j]->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                // any atoms before atom j should be in earlier itereations, check this by a constraint on the iteration number
                                for (size_t k = 0; k < j; k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // set an execution plan so the diff_plus version of the relation is evaluated first
                                // get existing execution plan
                                AstExecutionPlan* plan;
                                if (r1->getExecutionPlan() != nullptr) {
                                    plan = r1->getExecutionPlan()->clone();
                                } else {
                                    plan = new AstExecutionPlan();
                                }

                                plan->setOrderFor(version, diffVersion, std::move(createReordering(*r1, atoms.size() + 1, version, diffVersion)));
                                r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

                                // std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }
                            diffVersion++;
                        }
                    } else if (isDeletionRule) {
                        diffVersion = 1;
                        for (size_t i = 0; i < atoms.size(); i++) {
                            // a deletion rule should look as follows:
                            // diff_minus_R :- R_1, R_2, ..., diff_minus_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            std::unique_ptr<AstClause> rdiff(cl->clone());

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffMinusRelation(rel)->get()->getName());

                            /*
                            // ensure i-th tuple did not exist previously, this prevents double insertions
                            auto noPrevious = atoms[i]->clone();
                            noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                            */

                            // the current version of the rule should have diff_minus_count in the i-th position
                            // rdiff->getAtoms()[i]->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[i], program))->get()->getName());
                            rdiff->getAtoms()[i]->setName(translateActualDiffMinusRelation(getAtomRelation(atoms[i], program))->get()->getName());

                            /*
                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 2)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));
                                        */

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                        std::unique_ptr<AstArgument>(atoms[i]->getArgument(atoms[i]->getArity() - 1)->clone()),
                                        std::make_unique<AstNumberConstant>(0)));

                            // atoms before the i-th position should not fulfill the conditions for incremental insertion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));
                            }

                            for (size_t j = i + 1; j < atoms.size(); j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                // standard relation has the same tuples as diff_minus_applied, just with different counts
                                rdiff->getAtoms()[j]->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                            }

                            for (size_t j = 0; j < atoms.size(); j++) {
                                // add a constraint saying that the tuples must have existed previously
                                if (j != i) {
                                    rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                                std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                                std::make_unique<AstNumberConstant>(0)));
                                }

                                // add a constraint saying that the delta tuple can't have existed previously
                                auto noPrior = atoms[j]->clone();
                                // noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                auto negatedAtom = negations[j]->getAtom()->clone();
                                // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_minus
                            rdiff->getHead()->setName(translateNewDiffMinusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // tuple j should be in the previous iteration, simulating delta relations
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                // any atoms before atom j should be in earlier itereations, check this by a constraint on the iteration number
                                for (size_t k = 0; k < j; k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // set an execution plan so the diff_plus version of the relation is evaluated first
                                // get existing execution plan
                                AstExecutionPlan* plan;
                                if (r1->getExecutionPlan() != nullptr) {
                                    plan = r1->getExecutionPlan()->clone();
                                } else {
                                    plan = new AstExecutionPlan();
                                }

                                /*
                                if (plan->hasOrderFor(version, diffVersion)) {
                                    auto existingOrder = plan->getOrderFor(version, diffVersion);

                                    // extend in the case of extra atoms
                                    for (int k = existingOrder.size(); k < r1->getAtoms().size(); k++) {
                                        existingOrder.appendAtomIndex(k + 1);
                                    }
                                    plan->setOrderFor(version, diffVersion, std::move(createReordering(existingOrder, diffVersion)));
                                } else {
                                    AstExecutionOrder existingOrder;
                                    for (size_t k = 0; k < r1->getAtoms().size(); k++) {
                                        existingOrder.appendAtomIndex(k + 1);
                                    }
                                    plan->setOrderFor(version, diffVersion, std::move(createReordering(existingOrder, diffVersion)));
                                }
                                */

                                plan->setOrderFor(version, diffVersion, std::move(createReordering(*r1, diffVersion, version, diffVersion)));
                                r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

                                // std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }

                            diffVersion++;
                        }

                        diffVersion = atoms.size() + 1;
                        // TODO: if there is a negation, then we need to add a version of the rule which applies when only the negations apply
                        for (size_t i = 0; i < negations.size(); i++) {
                            // an insertion rule should look as follows:
                            // R :- R_1, R_2, ..., diff_plus_count_R_i, diff_applied_R_i+1, ..., diff_applied_R_n

                            auto rdiff = cl->clone();

                            // set the head of the rule to be the diff relation
                            rdiff->getHead()->setName(translateDiffMinusRelation(rel)->get()->getName());

                            // clone the i-th negation's atom
                            // each negation needs to have either not existed, or be deleted
                            // for the non-existence case, we use a positive negation instead
                            auto negatedAtomNamed = negations[i]->getAtom()->clone();
                            /*
                            UnnamedVariableRenamer renamer;
                            negatedAtomNamed->apply(renamer);
                            */

                            auto negatedAtom = negatedAtomNamed->clone();

                            // negatedAtom->setName(translateDiffPlusCountRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            negatedAtom->setName(translateActualDiffPlusRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                            // negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstUnnamedVariable>());
                            negatedAtom->setArgument(negatedAtom->getArity() - 1, std::make_unique<AstVariable>("@negation_count"));
                            negatedAtom->setArgument(negatedAtom->getArity() - 2, std::make_unique<AstUnnamedVariable>());
                            // negatedAtom->setArgument(negatedAtom->getArity() - 3, std::make_unique<AstUnnamedVariable>());
                            rdiff->addToBody(std::unique_ptr<AstAtom>(negatedAtom));

                            rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                        std::make_unique<AstVariable>("@negation_count"),
                                        std::make_unique<AstNumberConstant>(0)));

                            /*
                            // prevent double insertions across epochs
                            auto noPrevious = negatedAtomNamed->clone();
                            noPrevious->setName(translateRelation(getAtomRelation(noPrevious, program))->get()->getName());
                            noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                            // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                            // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                            rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrevious)));
                            */

                            // atoms before the i-th position should not fulfill the conditions for incremental deletion, otherwise we will have double insertions
                            for (size_t j = 0; j < i; j++) {
                                // rdiff->getAtoms()[j]->setName(translateDiffMinusAppliedRelation(getAtomRelation(atoms[i], program))->get()->getName());

                                // ensure tuple is not actually inserted
                                auto curAtom = negations[j]->getAtom()->clone();
                                // curAtom->setName(translateDiffPlusCountRelation(getAtomRelation(curAtom, program))->get()->getName());
                                curAtom->setName(translateDiffPlusRelation(getAtomRelation(curAtom, program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(0));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(0));

                                // also ensure tuple existed previously
                                auto noPrevious = negations[j]->getAtom()->clone();
                                noPrevious->setName(translateRelation(getAtomRelation(noPrevious, program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));
                            }

                            // process negations
                            for (size_t j = 0; j < negations.size(); j++) {
                                // each negation needs to have either not existed, or be deleted
                                // for the non-existence case, we use a positive negation instead
                                AstAtom* negatedAtom;
                                /*
                                if (j == i) {
                                    negatedAtom = negatedAtomNamed->clone();
                                } else {
                                */
                                    negatedAtom = negations[j]->getAtom()->clone();
                                // }
                                // negatedAtom->setName(translateDiffAppliedRelation(getAtomRelation(negatedAtom, program))->get()->getName());
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(negatedAtom)));
                            }

                            for (size_t j = 0; j < atoms.size(); j++) {
                                // ensure tuple is not actually inserted
                                auto curAtom = atoms[j]->clone();
                                // curAtom->setName(translateDiffMinusCountRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                curAtom->setName(translateDiffMinusRelation(getAtomRelation(atoms[j], program))->get()->getName());

                                curAtom->setArgument(curAtom->getArity() - 1, std::make_unique<AstNumberConstant>(-1));
                                // curAtom->setArgument(curAtom->getArity() - 2, std::make_unique<AstNumberConstant>(-1));

                                // also ensure tuple existed previously
                                auto noPrevious = atoms[j]->clone();
                                noPrevious->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrevious->setArgument(noPrevious->getArity() - 1, std::make_unique<AstNumberConstant>(1));
                                // noPrevious->setArgument(noPrevious->getArity() - 2, std::make_unique<AstNumberConstant>(0));
                                // noPrevious->setArgument(noPrevious->getArity() - 3, std::make_unique<AstUnnamedVariable>());

                                rdiff->addToBody(std::make_unique<AstDisjunctionConstraint>(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)), std::make_unique<AstExistenceCheck>(std::unique_ptr<AstAtom>(noPrevious))));
                                // rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(curAtom)));

                                // ensure the tuple existed previously
                                rdiff->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                                            std::unique_ptr<AstArgument>(atoms[j]->getArgument(atoms[j]->getArity() - 1)->clone()),
                                            std::make_unique<AstNumberConstant>(0)));

                                // add a constraint saying that the delta tuple can't have existed previously
                                auto noPrior = atoms[j]->clone();
                                // noPrior->setName(translateDiffAppliedRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                noPrior->setArgument(noPrior->getArity() - 1, std::make_unique<AstNumberConstant>(2));
                                rdiff->addToBody(std::make_unique<AstPositiveNegation>(std::unique_ptr<AstAtom>(noPrior)));
                            }

                            rdiff->clearNegations();

                            // create a subsumption negation so we don't re-insert previously discovered tuples
                            auto diffAppliedHeadAtom = cl->getHead()->clone();
                            diffAppliedHeadAtom->setName(translateDiffAppliedRelation(getAtomRelation(diffAppliedHeadAtom, program))->get()->getName());

                            // write into new_diff_plus
                            rdiff->getHead()->setName(translateNewDiffMinusRelation(rel)->get()->getName());

                            // if we have incremental evaluation, we use iteration counts to simulate delta relations
                            // rather than explicitly having a separate relation
                            rdiff->addToBody(std::make_unique<AstSubsumptionNegation>(
                                    std::unique_ptr<AstAtom>(diffAppliedHeadAtom), 1));

                            version = 0;
                            // use delta versions of relations for semi-naive evaluation
                            for (size_t j = 0; j < atoms.size(); j++) {
                                if (!isInSameSCC(getAtomRelation(atoms[j], program))) {
                                    continue;
                                }

                                // create clone
                                std::unique_ptr<AstClause> r1(rdiff->clone());

                                // r1->getAtoms()[j]->setName(translateDeltaRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->getAtoms()[j]->setName(translateRelation(getAtomRelation(atoms[j], program))->get()->getName());
                                r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                                            // std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 3)->clone()),
                                            std::unique_ptr<AstArgument>(r1->getAtoms()[j]->getArgument(r1->getAtoms()[j]->getArity() - 2)->clone()),
                                            std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));

                                // any atoms before atom j should be in earlier itereations, check this by a constraint on the iteration number
                                for (size_t k = 0; k < j; k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LE,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // any atoms after atom j should not be in delta, check this by a constraint on the iteration number
                                for (size_t k = j + 1; k < atoms.size(); k++) {
                                    if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                                        r1->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                                                    // std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 3)->clone()),
                                                    std::unique_ptr<AstArgument>(r1->getAtoms()[k]->getArgument(r1->getAtoms()[k]->getArity() - 2)->clone()),
                                                    std::make_unique<AstIntrinsicFunctor>(FunctorOp::SUB, std::make_unique<AstIterationNumber>(), std::make_unique<AstNumberConstant>(1))));
                                    }
                                }

                                // set an execution plan so the diff_plus version of the relation is evaluated first
                                // get existing execution plan
                                AstExecutionPlan* plan;
                                if (r1->getExecutionPlan() != nullptr) {
                                    plan = r1->getExecutionPlan()->clone();
                                } else {
                                    plan = new AstExecutionPlan();
                                }
                                /*
                                if (plan->hasOrderFor(version, diffVersion)) {
                                    auto existingOrder = plan->getOrderFor(version, diffVersion);

                                    // extend in the case of extra atoms
                                    for (int k = existingOrder.size(); k < r1->getAtoms().size(); k++) {
                                        existingOrder.appendAtomIndex(k + 1);
                                    }
                                    plan->setOrderFor(version, diffVersion, std::move(createReordering(existingOrder, diffVersion)));
                                } else {
                                    AstExecutionOrder existingOrder;
                                    for (size_t k = 0; k < r1->getAtoms().size(); k++) {
                                        existingOrder.appendAtomIndex(k + 1);
                                    }
                                    plan->setOrderFor(version, diffVersion, std::move(createReordering(existingOrder, diffVersion)));
                                }
                                */

                                plan->setOrderFor(version, diffVersion, std::move(createReordering(*r1, atoms.size() + 1, version, diffVersion)));
                                r1->setExecutionPlan(std::unique_ptr<AstExecutionPlan>(plan));

                                // std::cout << "recursive: " << *r1 << std::endl;

                                // translate rdiff
                                std::unique_ptr<RamStatement> rule = ClauseTranslator(*this).translateClause(*r1, *cl, version, diffVersion);

                                // add logging
                                if (Global::config().has("profile")) {
                                    const std::string& relationName = toString(rel->getName());
                                    const SrcLocation& srcLocation = r1->getSrcLoc();
                                    const std::string clText = stringify(toString(*r1));
                                    const std::string logTimerStatement =
                                            LogStatement::tRecursiveRule(relationName, version, srcLocation, clText);
                                    const std::string logSizeStatement =
                                            LogStatement::nRecursiveRule(relationName, version, srcLocation, clText);
                                    rule = std::make_unique<RamSequence>(std::make_unique<RamLogRelationTimer>(std::move(rule),
                                            logTimerStatement, std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())));
                                }

                                // add debug info
                                std::ostringstream ds;
                                ds << toString(*r1) << "\nin file ";
                                ds << r1->getSrcLoc();
                                rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                                // add rule to result
                                appendStmt(loopRelSeq, std::move(rule));

                                version++;
                            }
                            diffVersion++;
                        }
                    }
                }
            } else {
                version = 0;
                for (size_t j = 0; j < atoms.size(); ++j) {
                    AstAtom* atom = atoms[j];
                    const AstRelation* atomRelation = getAtomRelation(atom, program);

                    // only interested in atoms within the same SCC
                    if (!isInSameSCC(atomRelation)) {
                        continue;
                    }

                    // modify the processed rule to use relDelta and write to relNew
                    std::unique_ptr<AstClause> r1(cl->clone());
                    r1->getHead()->setName(relNew[rel]->get()->getName());
                    // if we have incremental evaluation, we use iteration counts to simulate delta relations
                    // rather than explicitly having a separate relation
                    if (!Global::config().has("incremental")) {
                        r1->getAtoms()[j]->setName(relDelta[atomRelation]->get()->getName());
                    }
                    if (Global::config().has("provenance")) {
                        size_t numberOfHeights = rel->numberOfHeightParameters();
                        r1->addToBody(std::make_unique<AstSubsumptionNegation>(
                                std::unique_ptr<AstAtom>(cl->getHead()->clone()), 1 + numberOfHeights));
                    } else {
                        if (r1->getHead()->getArity() > 0)
                            r1->addToBody(std::make_unique<AstNegation>(
                                    std::unique_ptr<AstAtom>(cl->getHead()->clone())));
                    }

                    // replace wildcards with variables (reduces indices when wildcards are used in recursive
                    // atoms)
                    nameUnnamedVariables(r1.get());

                    // reduce R to P ...
                    for (size_t k = j + 1; k < atoms.size(); k++) {
                        if (isInSameSCC(getAtomRelation(atoms[k], program))) {
                            AstAtom* cur = r1->getAtoms()[k]->clone();
                            cur->setName(relDelta[getAtomRelation(atoms[k], program)]->get()->getName());
                            r1->addToBody(std::make_unique<AstNegation>(std::unique_ptr<AstAtom>(cur)));
                        }
                    }

                    std::unique_ptr<RamStatement> rule =
                            ClauseTranslator(*this).translateClause(*r1, *cl, version);

                    /* add logging */
                    if (Global::config().has("profile")) {
                        const std::string& relationName = toString(rel->getName());
                        const SrcLocation& srcLocation = cl->getSrcLoc();
                        const std::string clauseText = stringify(toString(*cl));
                        const std::string logTimerStatement =
                                LogStatement::tRecursiveRule(relationName, version, srcLocation, clauseText);
                        const std::string logSizeStatement =
                                LogStatement::nRecursiveRule(relationName, version, srcLocation, clauseText);
                        rule = std::make_unique<RamSequence>(
                                std::make_unique<RamLogRelationTimer>(std::move(rule), logTimerStatement,
                                        std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
                    }

                    // add debug info
                    std::ostringstream ds;
                    ds << toString(*cl) << "\nin file ";
                    ds << cl->getSrcLoc();
                    rule = std::make_unique<RamDebugInfo>(std::move(rule), ds.str());

                    // add to loop body
                    appendStmt(loopRelSeq, std::move(rule));

                    // increment version counter
                    version++;
                }
            }
            assert(cl->getExecutionPlan() == nullptr || version > cl->getExecutionPlan()->getMaxVersion());
        }

        // if there was no rule, continue
        if (!loopRelSeq) {
            continue;
        }

        // label all versions
        if (Global::config().has("profile")) {
            const std::string& relationName = toString(rel->getName());
            const SrcLocation& srcLocation = rel->getSrcLoc();
            const std::string logTimerStatement = LogStatement::tRecursiveRelation(relationName, srcLocation);
            const std::string logSizeStatement = LogStatement::nRecursiveRelation(relationName, srcLocation);
            loopRelSeq = std::make_unique<RamLogRelationTimer>(std::move(loopRelSeq), logTimerStatement,
                    std::unique_ptr<RamRelationReference>(relNew[rel]->clone()));
        }

        /* add rule computations of a relation to parallel statement */
        loopSeq->add(std::move(loopRelSeq));
    }


    if (Global::config().has("incremental")) {
        for (const AstRelation* rel : scc) {
            updateTable->add(
                    std::make_unique<RamSequence>(
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())),
                            std::make_unique<RamClear>(
                                    std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone()))));
        }
    }

    /* construct exit conditions for odd and even iteration */
    auto addCondition = [](std::unique_ptr<RamCondition>& cond, std::unique_ptr<RamCondition> clause) {
        cond = ((cond) ? std::make_unique<RamConjunction>(std::move(cond), std::move(clause))
                       : std::move(clause));
    };

    std::unique_ptr<RamCondition> exitCond;
    for (const AstRelation* rel : scc) {
        if (Global::config().has("incremental")) {
            addCondition(exitCond, std::make_unique<RamEmptinessCheck>(
                                           std::unique_ptr<RamRelationReference>(translateNewDiffPlusRelation(rel)->clone())));
            addCondition(exitCond, std::make_unique<RamEmptinessCheck>(
                                           std::unique_ptr<RamRelationReference>(translateNewDiffMinusRelation(rel)->clone())));
        } else {
            addCondition(exitCond, std::make_unique<RamEmptinessCheck>(
                                           std::unique_ptr<RamRelationReference>(relNew[rel]->clone())));
        }
    }

    if (Global::config().has("incremental")) {
        // this is already added in translateProgram
        ramProg->addSubroutine("scc_" + std::to_string(indexOfScc) + "_update_exit", makeIncrementalExitCondSubroutine(*maxIterRelationRef));
        std::vector<std::unique_ptr<RamExpression>> exitCondArgs;
        exitCondArgs.push_back(std::make_unique<RamIterationNumber>());
        addCondition(exitCond, std::make_unique<RamSubroutineCondition>("scc_" + std::to_string(indexOfScc) + "_update_exit", std::move(exitCondArgs)));
    }

    /* construct fixpoint loop  */
    std::unique_ptr<RamStatement> res;
    if (preamble) appendStmt(res, std::move(preamble));
    if (!loopSeq->getStatements().empty() && exitCond && clearTable && updateTable) {
        appendStmt(res, std::make_unique<RamLoop>(std::move(loopSeq), std::move(clearTable), 
                                std::make_unique<RamExit>(std::move(exitCond)), std::move(updateTable)));
    }
    if (postamble) {
        appendStmt(res, std::move(postamble));
    }
    if (res) return res;

    assert(false && "Not Implemented");
    return nullptr;
}

std::unique_ptr<RamStatement> AstTranslator::makeIncrementalCleanupSubroutine(const AstProgram& program) {
    // create a RamSequence for cleaning up all relations
    std::unique_ptr<RamStatement> cleanupSequence;

    for (const auto& relation : program.getRelations()) {
        if (relation->getName().getName().find("@info") != std::string::npos) {
            continue;
        }

        // update every tuple in relation so that the previous and current counts match
        // FOR t0 in relation:
        //   INSERT (t0.0, t0.2, ..., -1, -1)
        // insert -1 as both counts and handle this case in the B-Tree update method

        // make a RamRelationReference to be used to build the subroutine
        auto relationReference = translateRelation(relation);

        /*
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone())));
        // appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusAppliedRelation(relation)->clone())));

        // the subroutine needs to be built from inside out
        // build the insertion step first
        std::vector<std::unique_ptr<RamExpression>> updateTuple;
        
        // insert the original tuple
        for (size_t i = 0; i < relation->getArity() - 2; i++) {
            updateTuple.push_back(std::make_unique<RamTupleElement>(0, i));
        }

        // insert -1 for both counts
        updateTuple.push_back(std::make_unique<RamNumber>(-1));
        updateTuple.push_back(std::make_unique<RamNumber>(-1));

        // create the projection
        auto insertUpdate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)->clone()), std::move(updateTuple));

        // create a filter so we only update if the counts didn't match originally
        auto insertUpdateFilter = std::make_unique<RamFilter>(std::make_unique<RamConstraint>(BinaryConstraintOp::NE,
                    std::make_unique<RamTupleElement>(0, relation->getArity() - 2),
                    std::make_unique<RamTupleElement>(0, relation->getArity() - 1)),
                std::move(insertUpdate));


        // create the scan
        auto cleanupScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)->clone()), 0, std::move(insertUpdateFilter));
        appendStmt(cleanupSequence, std::make_unique<RamQuery>(std::move(cleanupScan)));
        */

        /*
        appendStmt(cleanupSequence, std::make_unique<RamMerge>(
                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)->clone()),
                    std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation))));


        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)->clone())));
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)->clone())));
        // appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusAppliedRelation(relation)->clone())));
        */

        appendStmt(cleanupSequence, std::make_unique<RamRelationLoad>(
                    std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone()),
                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation))));

    }

    return cleanupSequence;
}

std::unique_ptr<RamStatement> AstTranslator::makeIncrementalUpdateCleanupSubroutine(const AstProgram& program) {
    // create a RamSequence for cleaning up all relations
    std::unique_ptr<RamStatement> cleanupSequence;

    /* construct exit conditions for odd and even iteration */
    auto addCondition = [](std::unique_ptr<RamCondition>& cond, std::unique_ptr<RamCondition> clause) {
        cond = ((cond) ? std::make_unique<RamConjunction>(std::move(cond), std::move(clause))
                       : std::move(clause));
    };

    for (const auto& relation : program.getRelations()) {

        if (relation->getName().getName().find("@info") != std::string::npos) {
            continue;
        }

        // make a RamRelationReference to be used to build the subroutine
        auto relationReference = translateRelation(relation);

        // appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone())));

        /*
        // update every tuple in diff_applied relation so that the previous and current counts match
        // FOR t0 in diff_plus_relation:
        //   INSERT (t0.0, t0.2, ..., -1, -1) into diff_applied_relation
        // we scan over diff_plus because we only want to update the tuples that have changed this epoch
        // insert -1 as both counts and handle this case in the B-Tree update method
        {
            // the subroutine needs to be built from inside out
            // build the insertion step first
            std::vector<std::unique_ptr<RamExpression>> updateTuple;
            
            // insert the original tuple
            for (size_t i = 0; i < relation->getArity() - 2; i++) {
                updateTuple.push_back(std::make_unique<RamTupleElement>(0, i));
            }

            // insert -1 for both counts
            updateTuple.push_back(std::make_unique<RamNumber>(-1));
            updateTuple.push_back(std::make_unique<RamNumber>(-1));

            // create the projection into diff_applied
            auto insertUpdate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)->clone()), std::move(updateTuple));


            // create the scan over diff_plus
            auto cleanupScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)->clone()), 0, std::move(insertUpdate));
            appendStmt(cleanupSequence, std::make_unique<RamQuery>(std::move(cleanupScan)));
        }

        // update every tuple in diff_applied relation so that the previous and current counts match
        // FOR t0 in diff_minus_relation:
        //   INSERT (t0.0, t0.2, ..., -1, -1) into diff_applied_relation
        // we scan over diff_minus because we only want to update the tuples that have changed this epoch
        // insert -1 as both counts and handle this case in the B-Tree update method
        {
            // the subroutine needs to be built from inside out
            // build the insertion step first
            std::vector<std::unique_ptr<RamExpression>> updateTuple;
            
            // insert the original tuple
            for (size_t i = 0; i < relation->getArity() - 2; i++) {
                updateTuple.push_back(std::make_unique<RamTupleElement>(0, i));
            }

            // insert -1 for both counts
            updateTuple.push_back(std::make_unique<RamNumber>(-1));
            updateTuple.push_back(std::make_unique<RamNumber>(-1));

            // create the projection into diff_applied
            auto insertUpdate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)->clone()), std::move(updateTuple));


            // create the scan over diff_minus
            auto cleanupScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)->clone()), 0, std::move(insertUpdate));
            appendStmt(cleanupSequence, std::make_unique<RamQuery>(std::move(cleanupScan)));
        }
        */

        appendStmt(cleanupSequence,
                std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone()),
                        std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)->clone())));
        appendStmt(cleanupSequence,
                std::make_unique<RamMerge>(std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone()),
                        std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)->clone())));

        /*
        // update every tuple in diff_applied relation so that the previous and current counts match
        // FOR t0 in diff_plus_relation:
        //   INSERT (t0.0, t0.2, ..., -1, -1) into diff_applied_relation
        // we scan over diff_plus because we only want to update the tuples that have changed this epoch
        // insert -1 as both counts and handle this case in the B-Tree update method
        {
            // the subroutine needs to be built from inside out
            // build the insertion step first
            std::vector<std::unique_ptr<RamExpression>> updateTuple;
            
            // insert the original tuple
            for (size_t i = 0; i < relation->getArity() - 2; i++) {
                updateTuple.push_back(std::make_unique<RamTupleElement>(0, i));
            }

            // insert -1 for both counts
            updateTuple.push_back(std::make_unique<RamNumber>(-1));
            updateTuple.push_back(std::make_unique<RamNumber>(-1));

            // create the projection into diff_applied
            auto insertUpdate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone()), std::move(updateTuple));

            // create the scan over diff_plus
            auto cleanupScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)->clone()), 0, std::move(insertUpdate));
            appendStmt(cleanupSequence, std::make_unique<RamQuery>(std::move(cleanupScan)));
        }

        // update every tuple in diff_applied relation so that the previous and current counts match
        // FOR t0 in diff_minus_relation:
        //   INSERT (t0.0, t0.2, ..., -1, -1) into diff_applied_relation
        // we scan over diff_minus because we only want to update the tuples that have changed this epoch
        // insert -1 as both counts and handle this case in the B-Tree update method
        {
            // the subroutine needs to be built from inside out
            // build the insertion step first
            std::vector<std::unique_ptr<RamExpression>> updateTuple;
            
            // insert the original tuple
            for (size_t i = 0; i < relation->getArity() - 2; i++) {
                updateTuple.push_back(std::make_unique<RamTupleElement>(0, i));
            }

            // insert -1 for both counts
            updateTuple.push_back(std::make_unique<RamNumber>(-1));
            updateTuple.push_back(std::make_unique<RamNumber>(-1));

            // create the projection into diff_applied
            auto insertUpdate = std::make_unique<RamProject>(std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone()), std::move(updateTuple));

            // create the scan over diff_minus
            auto cleanupScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)->clone()), 0, std::move(insertUpdate));
            appendStmt(cleanupSequence, std::make_unique<RamQuery>(std::move(cleanupScan)));
        }
        */

            /*
        appendStmt(cleanupSequence, std::make_unique<RamRelationLoad>(
                    std::unique_ptr<RamRelationReference>(translateRelation(relation)->clone()),
                    std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation))));
                    */

        /* HANDLED BY makeIncrementalUpdateClearDiffsSubroutine
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateActualDiffPlusRelation(relation)->clone())));
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateActualDiffMinusRelation(relation)->clone())));

        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)->clone())));
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)->clone())));
        */
        // appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusAppliedRelation(relation)->clone())));
    }

    return cleanupSequence;
}

std::unique_ptr<RamStatement> AstTranslator::makeIncrementalUpdateClearDiffsSubroutine(const AstProgram& program) {
    // create a RamSequence for cleaning up all relations
    std::unique_ptr<RamStatement> cleanupSequence;

    for (const auto& relation : program.getRelations()) {

        if (relation->getName().getName().find("@info") != std::string::npos) {
            continue;
        }

        // make a RamRelationReference to be used to build the subroutine
        auto relationReference = translateRelation(relation);

        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateActualDiffPlusRelation(relation)->clone())));
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateActualDiffMinusRelation(relation)->clone())));

        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)->clone())));
        appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)->clone())));

        // appendStmt(cleanupSequence, std::make_unique<RamClear>(std::unique_ptr<RamRelationReference>(translateDiffMinusAppliedRelation(relation)->clone())));
    }

    return cleanupSequence;
}

std::unique_ptr<RamStatement> AstTranslator::makeIncrementalExitCondSubroutine(const RamRelationReference& maxIterRelationRef) {
    // we want a subroutine that looks like:
    // FOR t0 in maxIterRel:
    //   IF t0.0 >= arg(iter):
    //     RETURN 0 NOW

    auto exitCondSequence = std::make_unique<RamSequence>();

    // make RamSubroutineReturnValue
    std::vector<std::unique_ptr<RamExpression>> returnFalseVal;
    returnFalseVal.push_back(std::make_unique<RamNumber>(0));
    auto returnFalse = std::make_unique<RamSubroutineReturnValue>(std::move(returnFalseVal), true);

    // make a RamCondition checking whether the maxIterRel tuple is > current iteration
    auto iterationConstraint = std::make_unique<RamConstraint>(BinaryConstraintOp::GE, std::make_unique<RamTupleElement>(0, 0), std::make_unique<RamSubroutineArgument>(0));

    // make RamFilter that returns false if the iteration number is greater
    auto iterationFilter = std::make_unique<RamFilter>(std::move(iterationConstraint), std::move(returnFalse));

    // create the RamScan
    auto exitCondScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(maxIterRelationRef.clone()), 0, std::move(iterationFilter));
    exitCondSequence->add(std::make_unique<RamQuery>(std::move(exitCondScan)));

    // default case
    std::vector<std::unique_ptr<RamExpression>> returnTrueVal;
    returnTrueVal.push_back(std::make_unique<RamNumber>(1));
    auto returnTrue = std::make_unique<RamSubroutineReturnValue>(std::move(returnTrueVal));
    exitCondSequence->add(std::make_unique<RamQuery>(std::move(returnTrue)));

    return exitCondSequence;
}

std::unique_ptr<RamStatement> AstTranslator::makeRelationSearchSubroutine(const RamRelationReference& rel) {
    auto searchSequence = std::make_unique<RamSequence>();

    auto addCondition = [](std::unique_ptr<RamCondition>& cond, std::unique_ptr<RamCondition> clause) {
        cond = ((cond) ? std::make_unique<RamConjunction>(std::move(cond), std::move(clause))
                       : std::move(clause));
    };

    // return the tuple if it's found
    std::vector<std::unique_ptr<RamExpression>> values;
    for (size_t i = 0; i < rel.get()->getArity(); i++) {
        values.push_back(std::make_unique<RamTupleElement>(0, i));
    }

    // check the tuple values match the subroutine arguments
    std::unique_ptr<RamCondition> checkMatchingTuple;
    for (size_t i = 0; i < rel.get()->getArity() - 2; i++) {
        addCondition(checkMatchingTuple, std::make_unique<RamConstraint>(BinaryConstraintOp::EQ,
                    std::make_unique<RamSubroutineArgument>(i), std::make_unique<RamTupleElement>(0, i)));
    }

    // oh god it's just special cases on top of special cases :) this one says
    // that for non-diff relations, we should check that the tuple has positive
    // count
    if (rel.get()->getName().find("actual_diff_") == std::string::npos) {
        addCondition(checkMatchingTuple, std::make_unique<RamConstraint>(BinaryConstraintOp::GT,
                    std::make_unique<RamTupleElement>(0, rel.get()->getArity() - 1), std::make_unique<RamNumber>(0)));
    }

    auto matchingTupleFilter = std::make_unique<RamFilter>(std::move(checkMatchingTuple), std::make_unique<RamSubroutineReturnValue>(std::move(values), true));

    // scan the relation
    auto scan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(rel.clone()), 0, std::move(matchingTupleFilter));

    return std::make_unique<RamQuery>(std::move(scan));
}

/*
std::unique_ptr<RamStatement> AstTranslator::makeSubproofSubroutine(const AstRelation& rel, const std::set<const AstRelation*> scc) {
    std::unique_ptr<RamStatement> res;

        for (size_t i = 0; i < rel->getArity() - 1; i++) {
            searchTuple.push_back(std::make_unique<RamTupleElement>(0, i));
        }
        searchTuple.push_back(std::make_unique<RamNumber>(2));

        // create a RamPositiveExistenceCheck
        auto existenceCheck = std::make_unique<RamPositiveExistenceCheck>(translateDiffAppliedRelation(rel), std::move(searchTuple));

        // create a RamFilter that returns false if the tuple doesn't exist
        auto returnTrueFilter = std::make_unique<RamFilter>(std::make_unique<RamNegation>(std::move(existenceCheck)), makeBoolReturn(false));

        // create a Scan that goes through diff_applied
        auto existenceScan = std::make_unique<RamScan>(translateNewDiffAppliedRelation(rel), 0, std::move(returnTrueFilter));

        // add to exitCondSequence
        appendStmt(exitCondSequence, std::make_unique<RamQuery>(std::move(existenceScan)));
    }

    appendStmt(exitCondSequence, std::make_unique<RamQuery>(makeBoolReturn(true)));

    return exitCondSequence;
}

std::unique_ptr<RamStatement> AstTranslator::makeIncrementalUpdateExitCondSubroutine(const std::set<const AstRelation*>& scc, const RamRelationReference& maxIterRelationRef) {
    // we want a subroutine that looks like:
    // FOR t0 in diff_applied_R1:
    //   IF t0 in R1 with positive count:
    //     RETURN 0 NOW
    // FOR t0 in diff_applied_R2:
    //   IF t0 in R2 with positive count:
    //     RETURN 0 NOW
    // ...
    // RETURN 1 NOW

    auto makeBoolReturn = [&](bool val) {
        // make RamSubroutineReturnValue
        std::vector<std::unique_ptr<RamExpression>> returnVal;
        if (val) {
            returnVal.push_back(std::make_unique<RamNumber>(1));
        } else {
            returnVal.push_back(std::make_unique<RamNumber>(0));
        }
        return std::make_unique<RamSubroutineReturnValue>(std::move(returnVal), true);
    };

    std::unique_ptr<RamStatement> exitCondSequence;

    // make a RamCondition checking whether the maxIterRel tuple is > current iteration
    std::vector<std::unique_ptr<RamExpression>> numbers;
    numbers.push_back(std::make_unique<RamSubroutineArgument>(0));
    numbers.push_back(std::make_unique<RamNumber>(1));
    auto iterationConstraint = std::make_unique<RamConstraint>(BinaryConstraintOp::GE, std::make_unique<RamTupleElement>(0, 0), std::make_unique<RamIntrinsicOperator>(FunctorOp::SUB, std::move(numbers)));

    // auto iterationConstraint = std::make_unique<RamConstraint>(BinaryConstraintOp::GE, std::make_unique<RamTupleElement>(0, 0), std::make_unique<RamIntrinsicOperator>(FunctorOp::SUB, std::make_unique<RamSubroutineArgument>(0), std::make_unique<RamNumber>(1)));

    // make RamFilter that returns false if the iteration number is greater
    auto iterationFilter = std::make_unique<RamFilter>(std::move(iterationConstraint), makeBoolReturn(false));

    // create the RamScan
    auto exitCondScan = std::make_unique<RamScan>(std::unique_ptr<RamRelationReference>(maxIterRelationRef.clone()), 0, std::move(iterationFilter));
    // exitCondSequence->add(std::make_unique<RamQuery>(std::move(exitCondScan)));
    appendStmt(exitCondSequence, std::make_unique<RamQuery>(std::move(exitCondScan)));

    // for each relation create a loop filter
    for (const auto* rel : scc) {

        // create a PositiveExistenceCheck search
        // start with a vector of RamExpressions
        std::vector<std::unique_ptr<RamExpression>> searchTuple;

        for (size_t i = 0; i < rel->getArity() - 1; i++) {
            searchTuple.push_back(std::make_unique<RamTupleElement>(0, i));
        }
        searchTuple.push_back(std::make_unique<RamNumber>(2));

        // create a RamPositiveExistenceCheck
        auto existenceCheck = std::make_unique<RamPositiveExistenceCheck>(translateDiffAppliedRelation(rel), std::move(searchTuple));

        // create a RamFilter that returns false if the tuple doesn't exist
        auto returnTrueFilter = std::make_unique<RamFilter>(std::make_unique<RamNegation>(std::move(existenceCheck)), makeBoolReturn(false));

        // create a Scan that goes through diff_applied
        auto existenceScan = std::make_unique<RamScan>(translateNewDiffPlusRelation(rel), 0, std::move(returnTrueFilter));

        // add to exitCondSequence
        appendStmt(exitCondSequence, std::make_unique<RamQuery>(std::move(existenceScan)));
    }

    appendStmt(exitCondSequence, std::make_unique<RamQuery>(makeBoolReturn(true)));

    return exitCondSequence;
}
*/

std::unique_ptr<RamStatement> AstTranslator::makeSubproofSubroutine(const AstRelation& rel, const std::set<const AstRelation*> scc) {
    std::unique_ptr<RamStatement> res;

    // make a subroutine for each clause
    for (auto clause : rel.getClauses()) {
        if (clause->getAtoms().size() > 0 && *(clause->getHead()->getArgument(rel.getArity() - 1)) == AstNumberConstant(1)) {
            appendStmt(res, makeSubproofSubroutine(*clause, scc));
        }
    }

    if (res) {
        std::cout << "subroutine: " << *res << std::endl;
    }

    return res;
}

/** make a subroutine to search for subproofs */
std::unique_ptr<RamStatement> AstTranslator::makeSubproofSubroutine(const AstClause& clause, const std::set<const AstRelation*> scc) {
    // create a utility to check SCC membership
    auto isInSameSCC = [&](const AstRelation* rel) {
        return std::find(scc.begin(), scc.end(), rel) != scc.end();
    };

    // make intermediate clause with constraints
    std::unique_ptr<AstClause> intermediateClause(clause.clone());

    // name unnamed variables
    nameUnnamedVariables(intermediateClause.get());

    // add constraint for each argument in head of atom
    AstAtom* head = intermediateClause->getHead();
    size_t numberOfHeights = program->getRelation(head->getName())->numberOfHeightParameters();
    for (size_t i = 0; i < head->getArguments().size() - 1 - numberOfHeights; i++) {
        auto arg = head->getArgument(i);

        if (auto var = dynamic_cast<AstVariable*>(arg)) {
            intermediateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(var->clone()), std::make_unique<AstSubroutineArgument>(i)));
        } else if (auto func = dynamic_cast<AstFunctor*>(arg)) {
            intermediateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(func->clone()), std::make_unique<AstSubroutineArgument>(i)));
        } else if (auto rec = dynamic_cast<AstRecordInit*>(arg)) {
            intermediateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                    std::unique_ptr<AstArgument>(rec->clone()), std::make_unique<AstSubroutineArgument>(i)));
        }
    }

    if (Global::config().get("provenance") == "subtreeHeights") {
        // starting index of subtree level arguments in argument list
        // starts immediately after original arguments as height and rulenumber of tuple are not passed to
        // subroutine
        size_t levelIndex = head->getArguments().size() - numberOfHeights - 1;

        // add level constraints
        for (size_t i = 0; i < intermediateClause->getBodyLiterals().size(); i++) {
            auto lit = intermediateClause->getBodyLiteral(i);
            if (auto atom = dynamic_cast<AstAtom*>(lit)) {
                auto arity = atom->getArity();
                auto literalHeights = program->getRelation(atom->getName())->numberOfHeightParameters();
                auto literalLevelIndex = arity - literalHeights;

                intermediateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::EQ,
                        std::unique_ptr<AstArgument>(atom->getArgument(literalLevelIndex)->clone()),
                        std::make_unique<AstSubroutineArgument>(levelIndex)));
            }
            levelIndex++;
        }
    } else {
        // index of level argument in argument list
        size_t levelIndex = head->getArguments().size() - numberOfHeights - 1;

        // intermediateClause->getHead()->setName(translateDiffAppliedRelation(getAtomRelation(intermediateClause->getHead(), program))->get()->getName());

        // add level constraints
        for (size_t i = 0; i < intermediateClause->getBodyLiterals().size(); i++) {
            auto lit = intermediateClause->getBodyLiteral(i);
            if (auto atom = dynamic_cast<AstAtom*>(lit)) {
                // intermediateClause->getAtoms()[i]->setName(translateDiffAppliedRelation(getAtomRelation(atom, program))->get()->getName());

                auto arity = atom->getArity();

                // arity - 1 is the count in body atoms
                intermediateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::GT,
                        std::unique_ptr<AstArgument>(atom->getArgument(arity - 1)->clone()),
                        std::make_unique<AstNumberConstant>(0)));

                if (isInSameSCC(getAtomRelation(atom, program))) {
                    // arity - 1 is the level number in body atoms
                    intermediateClause->addToBody(std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::LT,
                            std::unique_ptr<AstArgument>(atom->getArgument(arity - 2)->clone()),
                            std::make_unique<AstSubroutineArgument>(levelIndex)));
                }
            }
        }
    }

    std::cout << "producing subproof from clause " << *intermediateClause << std::endl;

    return ProvenanceClauseTranslator(*this).translateClause(*intermediateClause, clause);
}

/** make a subroutine to search for subproofs for the non-existence of a tuple */
std::unique_ptr<RamStatement> AstTranslator::makeNegationSubproofSubroutine(const AstClause& clause) {
    // TODO (taipan-snake): Currently we only deal with atoms (no constraints or negations or aggregates
    // or anything else...)

    // clone clause for mutation
    auto clauseReplacedAggregates = std::unique_ptr<AstClause>(clause.clone());

    int aggNumber = 0;
    struct AggregatesToVariables : public AstNodeMapper {
        int& aggNumber;

        AggregatesToVariables(int& aggNumber) : aggNumber(aggNumber) {}

        std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
            if (dynamic_cast<AstAggregator*>(node.get())) {
                return std::make_unique<AstVariable>("agg_" + std::to_string(aggNumber++));
            }

            node->apply(*this);
            return node;
        }
    };

    AggregatesToVariables aggToVar(aggNumber);
    clauseReplacedAggregates->apply(aggToVar);

    // build a vector of unique variables
    std::vector<const AstVariable*> uniqueVariables;

    visitDepthFirst(*clauseReplacedAggregates, [&](const AstVariable& var) {
        if (var.getName().find("@level_num") == std::string::npos) {
            // use find_if since uniqueVariables stores pointers, and we need to dereference the pointer to
            // check equality
            if (std::find_if(uniqueVariables.begin(), uniqueVariables.end(),
                        [&](const AstVariable* v) { return *v == var; }) == uniqueVariables.end()) {
                uniqueVariables.push_back(&var);
            }
        }
    });

    // a mapper to replace variables with subroutine arguments
    struct VariablesToArguments : public AstNodeMapper {
        const std::vector<const AstVariable*>& uniqueVariables;

        VariablesToArguments() = default;
        VariablesToArguments(const std::vector<const AstVariable*>& uniqueVariables)
                : uniqueVariables(uniqueVariables) {}

        std::unique_ptr<AstNode> operator()(std::unique_ptr<AstNode> node) const override {
            // replace unknown variables
            if (auto varPtr = dynamic_cast<const AstVariable*>(node.get())) {
                if (varPtr->getName().find("@level_num") == std::string::npos) {
                    size_t argNum = std::find_if(uniqueVariables.begin(), uniqueVariables.end(),
                                            [&](const AstVariable* v) { return *v == *varPtr; }) -
                                    uniqueVariables.begin();

                    return std::make_unique<AstSubroutineArgument>(argNum);
                } else {
                    return std::make_unique<AstUnnamedVariable>();
                }
            }

            // apply recursive
            node->apply(*this);

            // otherwise nothing
            return node;
        }
    };

    // the structure of this subroutine is a sequence where each nested statement is a search in each
    // relation
    std::unique_ptr<RamSequence> searchSequence = std::make_unique<RamSequence>();

    // make a copy so that when we mutate clause, pointers to objects in newClause are not affected
    auto newClause = std::unique_ptr<AstClause>(clauseReplacedAggregates->clone());

    // go through each body atom and create a return
    size_t litNumber = 0;
    for (const auto& lit : newClause->getBodyLiterals()) {
        if (auto atom = dynamic_cast<AstAtom*>(lit)) {
            size_t numberOfHeights = program->getRelation(atom->getName())->numberOfHeightParameters();
            // get a RamRelationReference
            auto relRef = translateRelation(atom);

            // construct a query
            std::vector<std::unique_ptr<RamExpression>> query;

            // translate variables to subroutine arguments
            VariablesToArguments varsToArgs(uniqueVariables);
            atom->apply(varsToArgs);

            // add each value (subroutine argument) to the search query
            for (size_t i = 0; i < atom->getArity() - 1 - numberOfHeights; i++) {
                auto arg = atom->getArgument(i);
                query.push_back(translateValue(arg, ValueIndex()));
            }

            // fill up query with nullptrs for the provenance columns
            query.push_back(std::make_unique<RamUndefValue>());
            for (size_t h = 0; h < numberOfHeights; h++) {
                query.push_back(std::make_unique<RamUndefValue>());
            }

            // ensure the length of query tuple is correct
            assert(query.size() == atom->getArity() && "wrong query tuple size");

            // make the nested operation to return the atom number if it exists
            std::vector<std::unique_ptr<RamExpression>> returnValue;
            returnValue.push_back(std::make_unique<RamNumber>(litNumber));

            // create a search
            // a filter to find whether the current atom exists or not
            auto searchFilter = std::make_unique<RamFilter>(
                    std::make_unique<RamExistenceCheck>(
                            std::unique_ptr<RamRelationReference>(relRef->clone()), std::move(query)),
                    std::make_unique<RamSubroutineReturnValue>(std::move(returnValue)));

            // now, return the values of the atoms, with a separator
            // between atom number and atom
            std::vector<std::unique_ptr<RamExpression>> returnAtom;
            returnAtom.push_back(std::make_unique<RamUndefValue>());
            // the actual atom
            for (size_t i = 0; i < atom->getArity() - 1 - numberOfHeights; i++) {
                returnAtom.push_back(translateValue(atom->getArgument(i), ValueIndex()));
            }

            // chain the atom number and atom value together
            auto atomSequence = std::make_unique<RamSequence>();
            atomSequence->add(std::make_unique<RamQuery>(std::move(searchFilter)));
            atomSequence->add(std::make_unique<RamQuery>(
                    std::make_unique<RamSubroutineReturnValue>(std::move(returnAtom))));

            // append search to the sequence
            searchSequence->add(std::move(atomSequence));
        } else if (auto con = dynamic_cast<AstConstraint*>(lit)) {
            VariablesToArguments varsToArgs(uniqueVariables);
            con->apply(varsToArgs);

            // translate to a RamCondition
            auto condition = translateConstraint(con, ValueIndex());

            // create a return value
            std::vector<std::unique_ptr<RamExpression>> returnValue;
            returnValue.push_back(std::make_unique<RamNumber>(litNumber));

            // create a filter
            auto filter = std::make_unique<RamFilter>(
                    std::move(condition), std::make_unique<RamSubroutineReturnValue>(std::move(returnValue)));

            // now, return the values of the literal, with a separator
            // between atom number and atom
            std::vector<std::unique_ptr<RamExpression>> returnLit;
            returnLit.push_back(std::make_unique<RamUndefValue>());
            // add return values for binary constraints and negations
            if (auto binaryConstraint = dynamic_cast<AstBinaryConstraint*>(con)) {
                returnLit.push_back(translateValue(binaryConstraint->getLHS(), ValueIndex()));
                returnLit.push_back(translateValue(binaryConstraint->getRHS(), ValueIndex()));
            } else if (auto negation = dynamic_cast<AstNegation*>(con)) {
                auto vals = negation->getAtom()->getArguments();
                auto numberOfHeights =
                        program->getRelation(negation->getAtom()->getName())->numberOfHeightParameters();
                for (size_t i = 0; i < vals.size() - 1 - numberOfHeights; i++) {
                    returnLit.push_back(translateValue(vals[i], ValueIndex()));
                }
            }

            // chain the atom number and atom value together
            auto litSequence = std::make_unique<RamSequence>();
            litSequence->add(std::make_unique<RamQuery>(std::move(filter)));
            litSequence->add(std::make_unique<RamQuery>(
                    std::make_unique<RamSubroutineReturnValue>(std::move(returnLit))));

            // append search to the sequence
            searchSequence->add(std::move(litSequence));
        }

        litNumber++;
    }

    return std::move(searchSequence);
}

std::pair<std::vector<AstRelation*>, std::vector<AstAtom*>> AstTranslator::createIncrementalRediscoverFilters(const AstClause& clause, int clauseNum, const std::vector<unsigned int>& order, const AstProgram& program, const RecursiveClauses* recursiveClauses) {
    // create a set of relations that restrict each predicate for the re-discovery rule
    // if we have a rule like R(x, y) :- R1(x, z), R2(z, y)., then we wish to restrict this as:
    // R(x, y) :- R_R1(x), R1(x, z), R_R2(y), R2(z, y).

    std::vector<AstRelation*> coveringRelations;
    std::vector<AstAtom*> covering;

    /*
    auto clause = ClauseTranslator(*this).getReorderedClause(origClause, version, version2);

    if (clause == nullptr) {
        clause = std::unique_ptr<AstClause>(origClause.clone());
    }

    auto curCount = clause->getHead()->getArgument(clause->getHead()->getArity() - 1);
    auto curCountNum = dynamic_cast<AstNumberConstant*>(curCount);
    bool isReinsertionRule = *curCountNum == AstNumberConstant(2);

    // skip non-recursive rules and only process re-insertion rules
    if (!recursiveClauses->recursive(&origClause) || !isReinsertionRule) {
    // if (!recursiveClauses->recursive(&origClause)) {
        return std::make_pair(coveringRelations, covering);
    }
    */

    assert(order.size() >= clause.getAtoms().size() && "ordering doesn't match size of clause for creating filters");

    // store only the variables in the head of the rule
    size_t numHeadVariables = 0;
    for (auto arg : clause.getHead()->getArguments()) {
        if (auto var = dynamic_cast<AstVariable*>(arg)) {
            // headVariables.push_back(var);
            numHeadVariables++;
        }
    }

    // store the set of variables that are covered so far
    std::set<const AstVariable*> coveredVariables;

    // go through each atom in the body of the rule
    // for (size_t i = 0; i < clause->getAtoms().size(); i++) {
    for (auto i : order) {
        if (i > clause.getAtoms().size()) {
            continue;
        }

        auto atom = clause.getAtoms()[i - 1];

        // exit if we have covered everything
        if (coveredVariables.size() == numHeadVariables) {
            break;
        }

        std::vector<AstVariable*> coversAtom;

        std::vector<int> variableNums;
        // find all variables in the head of the rule that match
        for (int j = 0; j < clause.getHead()->getArguments().size() - 2; j++) {
            if (auto var = dynamic_cast<AstVariable*>(clause.getHead()->getArguments()[j])) {
                bool covers = false;
                for (auto atomArg : atom->getArguments()) {
                    if (*var == *atomArg) {
                        covers = true;
                        break;
                    }
                }

                // don't duplicate variables
                if (covers) {
                    for (auto coveredVar : coveredVariables) {
                        if (*var == *coveredVar) {
                            covers = false;
                            break;
                        }
                    }
                }

                if (covers) {
                    // we need to cover this variable with a relation
                    coversAtom.push_back(var);

                    // add to the set of covered variables
                    coveredVariables.insert(var);

                    // record the number of this atom
                    variableNums.push_back(j);
                }
            }
        }

        /*
        std::cout << *atom << " is covered by: " << std::endl;
        for (auto var : coversAtom) {
            std::cout << *var << std::endl;
        }
        */

        if (coversAtom.size() > 0) {
            // create a restricting AstAtom
            auto restrictionName = toString(join(clause.getHead()->getName().getNames(), ".")) + "_@restricted_" + toString(join(variableNums, "_"));

            auto atomRelation = getAtomRelation(atom, &program);
            auto restrictionRelation = new AstRelation();
            restrictionRelation->setName(restrictionName);

            for (int j = 0; j < coversAtom.size(); j++) {
                restrictionRelation->addAttribute(std::unique_ptr<AstAttribute>(atomRelation->getAttribute(j)->clone()));
            }

            coveringRelations.push_back(restrictionRelation);

            auto restriction = new AstAtom(AstRelationIdentifier(restrictionName));
            for (auto var : coversAtom) {
                restriction->addArgument(std::unique_ptr<AstArgument>(var->clone()));
            }

            covering.push_back(restriction);
        }
    }

    return std::make_pair(coveringRelations, covering);
}

/** translates the given datalog program into an equivalent RAM program  */
void AstTranslator::translateProgram(const AstTranslationUnit& translationUnit) {
    // obtain type environment from analysis
    typeEnv = &translationUnit.getAnalysis<TypeEnvironmentAnalysis>()->getTypeEnvironment();

    // obtain recursive clauses from analysis
    const auto* recursiveClauses = translationUnit.getAnalysis<RecursiveClauses>();

    // obtain strongly connected component (SCC) graph from analysis
    const auto& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

    // obtain some topological order over the nodes of the SCC graph
    const auto& sccOrder = *translationUnit.getAnalysis<TopologicallySortedSCCGraph>();

    // obtain the schedule of relations expired at each index of the topological order
    const auto& expirySchedule = translationUnit.getAnalysis<RelationSchedule>()->schedule();

    // start with an empty sequence of ram statements
    std::unique_ptr<RamStatement> res = std::make_unique<RamSequence>();

    // start with an empty program
    ramProg = std::make_unique<RamProgram>(std::make_unique<RamSequence>());

    // handle the case of an empty SCC graph
    if (sccGraph.getNumberOfSCCs() == 0) return;

    // a function to load relations
    const auto& makeRamLoad = [&](std::unique_ptr<RamStatement>& current, const AstRelation* relation,
                                      const std::string& inputDirectory, const std::string& fileExtension) {
        std::unique_ptr<RamStatement> statement;
        if (Global::config().has("incremental")) {
            statement =
                std::make_unique<RamLoad>(std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)),
                        getInputIODirectives(relation, Global::config().get(inputDirectory), fileExtension));
        } else {
            statement =
                std::make_unique<RamLoad>(std::unique_ptr<RamRelationReference>(translateRelation(relation)),
                        getInputIODirectives(relation, Global::config().get(inputDirectory), fileExtension));
        }
        if (Global::config().has("profile")) {
            const std::string logTimerStatement =
                    LogStatement::tRelationLoadTime(toString(relation->getName()), relation->getSrcLoc());
            statement = std::make_unique<RamLogRelationTimer>(std::move(statement), logTimerStatement,
                    std::unique_ptr<RamRelationReference>(translateRelation(relation)));
        }
        appendStmt(current, std::move(statement));
    };

    // a function to store relations
    const auto& makeRamStore = [&](std::unique_ptr<RamStatement>& current, const AstRelation* relation,
                                       const std::string& outputDirectory, const std::string& fileExtension) {
        std::unique_ptr<RamStatement> statement = std::make_unique<RamStore>(
                std::unique_ptr<RamRelationReference>(translateRelation(relation)),
                getOutputIODirectives(relation, Global::config().get(outputDirectory), fileExtension));
        if (Global::config().has("profile")) {
            const std::string logTimerStatement =
                    LogStatement::tRelationSaveTime(toString(relation->getName()), relation->getSrcLoc());
            statement = std::make_unique<RamLogRelationTimer>(std::move(statement), logTimerStatement,
                    std::unique_ptr<RamRelationReference>(translateRelation(relation)));
        }
        appendStmt(current, std::move(statement));
    };

    // a function to drop relations
    const auto& makeRamDrop = [&](std::unique_ptr<RamStatement>& current, const AstRelation* relation) {
        appendStmt(current, std::make_unique<RamDrop>(translateRelation(relation)));
    };

    // maintain the index of the SCC within the topological order
    size_t indexOfScc = 0;

    // iterate over each SCC according to the topological order
    for (const auto& scc : sccOrder.order()) {
        // make a new ram statement for the current SCC
        std::unique_ptr<RamStatement> current;

        // find out if the current SCC is recursive
        const auto& isRecursive = sccGraph.isRecursive(scc);

        // make variables for particular sets of relations contained within the current SCC, and,
        // predecessors and successor SCCs thereof
        const auto& allInterns = sccGraph.getInternalRelations(scc);
        const auto& internIns = sccGraph.getInternalInputRelations(scc);
        const auto& internOuts = sccGraph.getInternalOutputRelations(scc);
        const auto& externOutPreds = sccGraph.getExternalOutputPredecessorRelations(scc);
        const auto& externNonOutPreds = sccGraph.getExternalNonOutputPredecessorRelations(scc);

        // const auto& externPreds = sccGraph.getExternalPredecessorRelations(scc);
        // const auto& internsWithExternSuccs = sccGraph.getInternalRelationsWithExternalSuccessors(scc);
        const auto& internNonOutsWithExternSuccs =
                sccGraph.getInternalNonOutputRelationsWithExternalSuccessors(scc);

        // make a variable for all relations that are expired at the current SCC
        const auto& internExps = expirySchedule.at(indexOfScc).expired();

        // create a utility to check SCC membership
        auto isInSameSCC = [&](const AstRelation* rel) {
            return std::find(allInterns.begin(), allInterns.end(), rel) != allInterns.end();
        };


        // create all internal relations of the current scc
        for (const auto& relation : allInterns) {
            if (Global::config().has("incremental")) {
                appendStmt(current, std::make_unique<RamCreate>(
                                            std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation))));
                appendStmt(current, std::make_unique<RamCreate>(
                                            std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation))));

                appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                            translateActualDiffPlusRelation(relation))));
                appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                            translateActualDiffMinusRelation(relation))));

                // ensure that diff_applied and diff_minus_applied are the last relation before the standard relation, so they can all share the same type
                appendStmt(current, std::make_unique<RamCreate>(
                                            std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation))));
                /*
                appendStmt(current, std::make_unique<RamCreate>(
                                            std::unique_ptr<RamRelationReference>(translateDiffMinusAppliedRelation(relation))));
                                            */
            }

            appendStmt(current, std::make_unique<RamCreate>(
                                        std::unique_ptr<RamRelationReference>(translateRelation(relation))));
            
            // create new and delta relations if required
            if (isRecursive) {
                if (Global::config().has("incremental")) {
                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                translateNewDiffAppliedRelation(relation))));
                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                translateDeltaDiffAppliedRelation(relation))));
                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                translateNewDiffPlusRelation(relation))));
                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                translateNewDiffMinusRelation(relation))));

                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                translateUpdatedMinusRelation(relation))));
                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                translateUpdatedPlusRelation(relation))));

                    /*
                    std::set<AstRelationIdentifier> processedRestrictionRelations;
                    for (size_t i = 0; i < relation->getClauses().size(); i++) {
                        auto clause = relation->getClauses()[i];
                        for (size_t j = 0; j < clause->getAtoms().size(); j++) {
                            if (!isInSameSCC(getAtomRelation(clause->getAtoms()[j], program))) {
                                continue;
                            }

                            auto restrictionAtoms = createIncrementalRediscoverFilters(*clause, i, j, clause->getAtoms().size() + clause->getNegations().size() + 1, *program, recursiveClauses);

                            for (AstRelation* restrictionRel : restrictionAtoms.first) {
                                if (!contains(processedRestrictionRelations, restrictionRel->getName())) {
                                    // if not already processed
                                    appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                                                translateRelation(restrictionRel))));
                                    processedRestrictionRelations.insert(restrictionRel->getName());
                                }
                            }
                        }
                    }
                    */
                }

                appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                            translateDeltaRelation(relation))));
                appendStmt(current, std::make_unique<RamCreate>(std::unique_ptr<RamRelationReference>(
                                            translateNewRelation(relation))));
            }
        }

        {
            // load all internal input relations from the facts dir with a .facts extension
            for (const auto& relation : internIns) {
                makeRamLoad(current, relation, "fact-dir", ".facts");
            }

            // if a communication engine has been specified...
            if (Global::config().has("engine")) {
                // load all external output predecessor relations from the output dir with a .csv
                // extension
                for (const auto& relation : externOutPreds) {
                    makeRamLoad(current, relation, "output-dir", ".csv");
                }
                // load all external output predecessor relations from the output dir with a .facts
                // extension
                for (const auto& relation : externNonOutPreds) {
                    makeRamLoad(current, relation, "output-dir", ".facts");
                }
            }
        }

        // compute the relations themselves
        std::unique_ptr<RamStatement> bodyStatement =
                (!isRecursive) ? translateNonRecursiveRelation(
                                         *((const AstRelation*)*allInterns.begin()), recursiveClauses)
                               : translateRecursiveRelation(allInterns, recursiveClauses, indexOfScc);
        appendStmt(current, std::move(bodyStatement));

        /*
        if (Global::config().has("incremental")) {
            // make merges for non-recursive relations
            if (!isRecursive) {
                for (const auto& relation : allInterns) {
                    // populate diff_applied relation
                    appendStmt(current, std::make_unique<RamMerge>(
                                std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation))));
                    appendStmt(current, std::make_unique<RamMerge>(
                                std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation))
                                ));
                }

            }
        }
        */

        {
            // if a communication engine is enabled...
            if (Global::config().has("engine")) {
                // store all internal non-output relations with external successors to the output dir with
                // a .facts extension
                for (const auto& relation : internNonOutsWithExternSuccs) {
                    makeRamStore(current, relation, "output-dir", ".facts");
                }
            }

            if (!Global::config().has("incremental")) {
                // store all internal output relations to the output dir with a .csv extension
                for (const auto& relation : internOuts) {
                    makeRamStore(current, relation, "output-dir", ".csv");
                }
            }
        }

        // if provenance is not enabled...
        if (!Global::config().has("provenance") && !Global::config().has("incremental")) {
            // if a communication engine is enabled...
            if (Global::config().has("engine")) {
                // drop all internal relations
                for (const auto& relation : allInterns) {
                    makeRamDrop(current, relation);
                }
                // drop external output predecessor relations
                for (const auto& relation : externOutPreds) {
                    makeRamDrop(current, relation);
                }
                // drop external non-output predecessor relations
                for (const auto& relation : externNonOutPreds) {
                    makeRamDrop(current, relation);
                }
            } else {
                // otherwise, drop all  relations expired as per the topological order
                for (const auto& relation : internExps) {
                    makeRamDrop(current, relation);
                }
            }
        }

        // add the cleanup subroutine
        if (Global::config().has("incremental") && indexOfScc == sccGraph.getNumberOfSCCs() - 1) {
            // make subroutine condition, don't actually use return value
            auto cleanupCond = std::make_unique<RamSubroutineCondition>("incremental_cleanup");

            // put it into a RamExit
            appendStmt(current, std::make_unique<RamExit>(std::move(cleanupCond), false));

            // process stores after cleanup
            for (const auto& scc : sccOrder.order()) {
                // store all internal output relations to the output dir with a .csv extension
                for (const auto& relation : sccGraph.getInternalOutputRelations(scc)) {
                    makeRamStore(current, relation, "output-dir", ".csv");
                }
            }
        }

        if (current) {
            // append the current SCC as a stratum to the sequence
            appendStmt(res, std::make_unique<RamStratum>(std::move(current), indexOfScc));

            // increment the index of the current SCC
            indexOfScc++;
        }

    }

    /*
    */

    // add main timer if profiling
    if (res && Global::config().has("profile")) {
        res = std::make_unique<RamLogTimer>(std::move(res), LogStatement::runtime());
    }

    // done for main prog
    ramProg->setMain(std::move(res));

    // add subroutines for each clause
    if (Global::config().has("provenance")) {
        visitDepthFirst(program->getRelations(), [&](const AstRelation& rel) {
            std::stringstream relName;
            relName << rel.getName();

            // do not add subroutines for info relations or facts
            if (relName.str().find("@info") != std::string::npos) {
                return;
            }

            std::string subroutineLabel = relName.str() + "_subproof";

            /*
            auto s = makeSubproofSubroutine(rel);

            if (s) {
                ramProg->addSubroutine(subroutineLabel, std::move(s));
            }
            */
        });

        visitDepthFirst(program->getRelations(), [&](const AstClause& clause) {
            std::stringstream relName;
            relName << clause.getHead()->getName();

            // do not add subroutines for info relations or facts
            if (relName.str().find("@info") != std::string::npos || clause.getBodyLiterals().empty()) {
                return;
            }

            /*
            std::string subroutineLabel =
                    relName.str() + "_" + std::to_string(clause.getClauseNum()) + "_subproof";
            ramProg->addSubroutine(subroutineLabel, makeSubproofSubroutine(clause));
            */

            std::string negationSubroutineLabel =
                    relName.str() + "_" + std::to_string(clause.getClauseNum()) + "_negation_subproof";
            ramProg->addSubroutine(negationSubroutineLabel, makeNegationSubproofSubroutine(clause));
        });
    }

    // add cleanup subroutine for incremental
    if (Global::config().has("incremental")) {
        // obtain strongly connected component (SCC) graph from analysis
        const auto& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

        for (const auto& scc : sccOrder.order()) {
            const auto& allInterns = sccGraph.getInternalRelations(scc);

            for (const auto& rel : allInterns) {
                std::stringstream relName;
                relName << rel->getName();

                // do not add subroutines for info relations or facts
                if (relName.str().find("@info") != std::string::npos) {
                    continue;
                }

                // std::string origName = relName.str().erase(relName.str().find("diff_applied@_"), 14);
                // std::cout << "subproof relation name: " << relName.str() << std::endl;

                std::string subroutineLabel = relName.str() + "_subproof";

                auto s = makeSubproofSubroutine(*rel, allInterns);

                if (s) {
                    ramProg->addSubroutine(subroutineLabel, std::move(s));
                }
            }
        }

        visitDepthFirst(program->getRelations(), [&](const AstRelation& rel) {
            std::stringstream relName;
            relName << rel.getName();

            // do not add subroutines for info relations or facts or nullaries
            if (relName.str().find("@info") != std::string::npos || rel.getArity() == 2) {
                return;
            }

            ramProg->addSubroutine(relName.str() + "_search", makeRelationSearchSubroutine(*translateRelation(&rel)));
            ramProg->addSubroutine("diff_plus_" + relName.str() + "_search", makeRelationSearchSubroutine(*translateActualDiffPlusRelation(&rel)));
            ramProg->addSubroutine("diff_minus_" + relName.str() + "_search", makeRelationSearchSubroutine(*translateActualDiffMinusRelation(&rel)));
        });

        ramProg->addSubroutine("incremental_cleanup", makeIncrementalCleanupSubroutine(*translationUnit.getProgram()));
    }
}

/** translates the given datalog program into an equivalent RAM program  */
void AstTranslator::translateUpdateProgram(const AstTranslationUnit& translationUnit) {
    // obtain type environment from analysis
    typeEnv = &translationUnit.getAnalysis<TypeEnvironmentAnalysis>()->getTypeEnvironment();

    // obtain recursive clauses from analysis
    const auto* recursiveClauses = translationUnit.getAnalysis<RecursiveClauses>();

    // obtain strongly connected component (SCC) graph from analysis
    const auto& sccGraph = *translationUnit.getAnalysis<SCCGraph>();

    // obtain some topological order over the nodes of the SCC graph
    const auto& sccOrder = *translationUnit.getAnalysis<TopologicallySortedSCCGraph>();

    // obtain the schedule of relations expired at each index of the topological order
    const auto& expirySchedule = translationUnit.getAnalysis<RelationSchedule>()->schedule();

    // start with an empty sequence of ram statements
    std::unique_ptr<RamStatement> res = std::make_unique<RamSequence>();

    // start with an empty program
    // ramProg = std::make_unique<RamProgram>(std::make_unique<RamSequence>());

    // handle the case of an empty SCC graph
    if (sccGraph.getNumberOfSCCs() == 0) return;

    // a function to load relations
    const auto& makeRamLoad = [&](std::unique_ptr<RamStatement>& current, const AstRelation* relation,
                                      const std::string& inputDirectory, const std::string& fileExtension) {
        std::unique_ptr<RamStatement> statement;
        if (Global::config().has("incremental")) {
            statement =
                std::make_unique<RamLoad>(std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)),
                        getInputIODirectives(relation, Global::config().get(inputDirectory), fileExtension));
        } else {
            statement =
                std::make_unique<RamLoad>(std::unique_ptr<RamRelationReference>(translateRelation(relation)),
                        getInputIODirectives(relation, Global::config().get(inputDirectory), fileExtension));
        }
        if (Global::config().has("profile")) {
            const std::string logTimerStatement =
                    LogStatement::tRelationLoadTime(toString(relation->getName()), relation->getSrcLoc());
            statement = std::make_unique<RamLogRelationTimer>(std::move(statement), logTimerStatement,
                    std::unique_ptr<RamRelationReference>(translateRelation(relation)));
        }
        appendStmt(current, std::move(statement));
    };

    // a function to store relations
    const auto& makeRamStore = [&](std::unique_ptr<RamStatement>& current, const AstRelation* relation,
                                       const std::string& outputDirectory, const std::string& fileExtension) {
        std::unique_ptr<RamStatement> statement = std::make_unique<RamStore>(
                std::unique_ptr<RamRelationReference>(translateRelation(relation)),
                getOutputIODirectives(relation, Global::config().get(outputDirectory), fileExtension));
        if (Global::config().has("profile")) {
            const std::string logTimerStatement =
                    LogStatement::tRelationSaveTime(toString(relation->getName()), relation->getSrcLoc());
            statement = std::make_unique<RamLogRelationTimer>(std::move(statement), logTimerStatement,
                    std::unique_ptr<RamRelationReference>(translateRelation(relation)));
        }
        appendStmt(current, std::move(statement));
    };

    // a function to drop relations
    const auto& makeRamDrop = [&](std::unique_ptr<RamStatement>& current, const AstRelation* relation) {
        appendStmt(current, std::make_unique<RamDrop>(translateRelation(relation)));
    };

    // maintain the index of the SCC within the topological order
    size_t indexOfScc = 0;

    // iterate over each SCC according to the topological order
    for (const auto& scc : sccOrder.order()) {
        // make a new ram statement for the current SCC
        std::unique_ptr<RamStatement> current;

        // find out if the current SCC is recursive
        const auto& isRecursive = sccGraph.isRecursive(scc);

        // make variables for particular sets of relations contained within the current SCC, and,
        // predecessors and successor SCCs thereof
        const auto& allInterns = sccGraph.getInternalRelations(scc);
        const auto& internIns = sccGraph.getInternalInputRelations(scc);
        const auto& internOuts = sccGraph.getInternalOutputRelations(scc);
        const auto& externOutPreds = sccGraph.getExternalOutputPredecessorRelations(scc);
        const auto& externNonOutPreds = sccGraph.getExternalNonOutputPredecessorRelations(scc);

        // const auto& externPreds = sccGraph.getExternalPredecessorRelations(scc);
        // const auto& internsWithExternSuccs = sccGraph.getInternalRelationsWithExternalSuccessors(scc);
        const auto& internNonOutsWithExternSuccs =
                sccGraph.getInternalNonOutputRelationsWithExternalSuccessors(scc);

        // make a variable for all relations that are expired at the current SCC
        const auto& internExps = expirySchedule.at(indexOfScc).expired();
        {
            // if a communication engine has been specified...
            if (Global::config().has("engine")) {
                // load all external output predecessor relations from the output dir with a .csv
                // extension
                for (const auto& relation : externOutPreds) {
                    makeRamLoad(current, relation, "output-dir", ".csv");
                }
                // load all external output predecessor relations from the output dir with a .facts
                // extension
                for (const auto& relation : externNonOutPreds) {
                    makeRamLoad(current, relation, "output-dir", ".facts");
                }
            }
        }

        // compute the relations themselves
        std::unique_ptr<RamStatement> bodyStatement =
                (!isRecursive) ? translateUpdateNonRecursiveRelation(
                                         *((const AstRelation*)*allInterns.begin()), recursiveClauses)
                               : translateUpdateRecursiveRelation(allInterns, recursiveClauses, indexOfScc);
        appendStmt(current, std::move(bodyStatement));

        if (Global::config().has("incremental")) {
            // make merges for non-recursive relations
            if (!isRecursive) {
                for (const auto& relation : allInterns) {
                    if (relation->getName().getName().find("@info") != std::string::npos) {
                        continue;
                    }

                    // populate diff_applied relation
                    appendStmt(current, std::make_unique<RamMerge>(
                                std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation))));
                    appendStmt(current, std::make_unique<RamMerge>(
                                std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation))
                                ));

                    appendStmt(current, std::make_unique<RamSemiMerge>(
                                std::unique_ptr<RamRelationReference>(translateActualDiffMinusRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffMinusRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffAppliedRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateUpdatedMinusRelation(relation))));
                    appendStmt(current, std::make_unique<RamSemiMerge>(
                                std::unique_ptr<RamRelationReference>(translateActualDiffPlusRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateDiffPlusRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateRelation(relation)),
                                std::unique_ptr<RamRelationReference>(translateUpdatedPlusRelation(relation))));
                }
            }
        }

        {
            // if a communication engine is enabled...
            if (Global::config().has("engine")) {
                // store all internal non-output relations with external successors to the output dir with
                // a .facts extension
                for (const auto& relation : internNonOutsWithExternSuccs) {
                    makeRamStore(current, relation, "output-dir", ".facts");
                }
            }

            if (!Global::config().has("incremental")) {
                // store all internal output relations to the output dir with a .csv extension
                for (const auto& relation : internOuts) {
                    makeRamStore(current, relation, "output-dir", ".csv");
                }
            }
        }

        // if provenance is not enabled...
        if (!Global::config().has("provenance") && !Global::config().has("incremental")) {
            // if a communication engine is enabled...
            if (Global::config().has("engine")) {
                // drop all internal relations
                for (const auto& relation : allInterns) {
                    makeRamDrop(current, relation);
                }
                // drop external output predecessor relations
                for (const auto& relation : externOutPreds) {
                    makeRamDrop(current, relation);
                }
                // drop external non-output predecessor relations
                for (const auto& relation : externNonOutPreds) {
                    makeRamDrop(current, relation);
                }
            } else {
                // otherwise, drop all  relations expired as per the topological order
                for (const auto& relation : internExps) {
                    makeRamDrop(current, relation);
                }
            }
        }

        // add the cleanup subroutine
        if (Global::config().has("incremental") && indexOfScc == sccGraph.getNumberOfSCCs() - 1) {
            // make subroutine condition, don't actually use return value
            auto cleanupCond = std::make_unique<RamSubroutineCondition>("incremental_update_cleanup");

            // put it into a RamExit
            appendStmt(current, std::make_unique<RamExit>(std::move(cleanupCond), false));

            // process stores after cleanup
            for (const auto& scc : sccOrder.order()) {
                // store all internal output relations to the output dir with a .csv extension
                for (const auto& relation : sccGraph.getInternalOutputRelations(scc)) {
                    makeRamStore(current, relation, "output-dir", ".csv");
                }
            }
        }

        if (current) {
            // append the current SCC as a stratum to the sequence
            appendStmt(res, std::make_unique<RamStratum>(std::move(current), indexOfScc));
        }

        // increment the index of the current SCC
        indexOfScc++;

    }

    /*
    */

    // add main timer if profiling
    if (res && Global::config().has("profile")) {
        res = std::make_unique<RamLogTimer>(std::move(res), LogStatement::runtime());
    }

    /*
    // done for main prog
    ramProg->setMain(std::move(res));
    */

    ramProg->addSubroutine("update", std::move(res));

    // this is already created in translateProgram
    // add cleanup subroutine for incremental
    if (Global::config().has("incremental")) {
        ramProg->addSubroutine("incremental_update_clear_diffs", makeIncrementalUpdateClearDiffsSubroutine(*translationUnit.getProgram()));
    }

    if (Global::config().has("incremental")) {
        ramProg->addSubroutine("incremental_update_cleanup", makeIncrementalUpdateCleanupSubroutine(*translationUnit.getProgram()));
    }
}

std::unique_ptr<RamTranslationUnit> AstTranslator::translateUnit(AstTranslationUnit& tu) {
    auto ram_start = std::chrono::high_resolution_clock::now();
    program = tu.getProgram();
    translateProgram(tu);
    translateUpdateProgram(tu);
    SymbolTable& symTab = tu.getSymbolTable();
    ErrorReport& errReport = tu.getErrorReport();
    DebugReport& debugReport = tu.getDebugReport();
    if (!Global::config().get("debug-report").empty()) {
        if (ramProg) {
            auto ram_end = std::chrono::high_resolution_clock::now();
            std::string runtimeStr =
                    "(" + std::to_string(std::chrono::duration<double>(ram_end - ram_start).count()) + "s)";
            std::stringstream ramProgStr;
            ramProgStr << *ramProg;
            debugReport.addSection(DebugReporter::getCodeSection(
                    "ram-program", "RAM Program " + runtimeStr, ramProgStr.str()));
        }
    }
    return std::make_unique<RamTranslationUnit>(std::move(ramProg), symTab, errReport, debugReport);
}

}  // end of namespace souffle
