/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2018 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnitTranslator.cpp
 *
 ***********************************************************************/

#include "ast2ram/incremental/update/UnitTranslator.h"
#include "ast2ram/incremental/Utils.h"
#include "Global.h"
#include "LogStatement.h"
#include "ast/BinaryConstraint.h"
#include "ast/Clause.h"
#include "ast/Constraint.h"
#include "ast/analysis/TopologicallySortedSCCGraph.h"
#include "ast/utility/Utils.h"
#include "ast/utility/Visitor.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ast2ram/utility/ValueIndex.h"
#include "ram/Call.h"
#include "ram/Clear.h"
#include "ram/Constraint.h"
#include "ram/Conjunction.h"
#include "ram/DebugInfo.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Exit.h"
#include "ram/Expression.h"
#include "ram/Filter.h"
#include "ram/IfNotExists.h"
#include "ram/Insert.h"
#include "ram/IterationNumber.h"
#include "ram/LogSize.h"
#include "ram/LogRelationTimer.h"
#include "ram/LogTimer.h"
#include "ram/MergeExtend.h"
#include "ram/Negation.h"
#include "ram/OperationSequence.h"
#include "ram/Query.h"
#include "ram/RelationSize.h"
#include "ram/Scan.h"
#include "ram/Sequence.h"
#include "ram/SignedConstant.h"
#include "ram/Statement.h"
#include "ram/StringConstant.h"
#include "ram/SubroutineArgument.h"
#include "ram/SubroutineReturn.h"
#include "ram/Swap.h"
#include "ram/TupleElement.h"
#include "ram/UndefValue.h"
#include "souffle/SymbolTable.h"
#include "souffle/utility/StringUtil.h"
#include <sstream>

namespace souffle::ast2ram::incremental::update {

void UnitTranslator::addRamSubroutine(std::string subroutineID, Own<ram::Statement> subroutine) {
    assert(!contains(updateRamSubroutines, subroutineID) && "subroutine ID should not already exist");
    updateRamSubroutines[subroutineID] = std::move(subroutine);
}

Own<ram::Sequence> UnitTranslator::generateProgram(const ast::TranslationUnit& translationUnit) {
    // Do the regular translation
    // auto ramProgram = seminaive::UnitTranslator::generateProgram(translationUnit);

    // auto ramProgram = mk<ram::Sequence>();
    // return ramProgram;

    // Generate context here
    context = mk<TranslatorContext>(translationUnit, true);

    const auto& sccOrdering =
            translationUnit.getAnalysis<ast::analysis::TopologicallySortedSCCGraphAnalysis>().order();

    std::cout << "scc ordering size: " << sccOrdering.size() << std::endl;

    // Create subroutines for each SCC according to topological order
    for (std::size_t i = 0; i < sccOrdering.size(); i++) {
        // Generate the main stratum code
        auto stratum = generateStratum(sccOrdering.at(i));

        // Clear expired relations
        const auto& expiredRelations = context->getExpiredRelations(i);
        stratum = mk<ram::Sequence>(std::move(stratum), generateClearExpiredRelations(expiredRelations));

        // Add the subroutine
        std::string stratumID = "update_stratum_" + toString(i);
        addRamSubroutine(stratumID, std::move(stratum));
    }

    // Invoke all strata
    VecOwn<ram::Statement> res;
    for (std::size_t i = 0; i < sccOrdering.size(); i++) {
        appendStmt(res, mk<ram::Call>("update_stratum_" + toString(i)));
    }

    // Add main timer if profiling
    if (!res.empty() && Global::config().has("profile")) {
        auto newStmt = mk<ram::LogTimer>(mk<ram::Sequence>(std::move(res)), LogStatement::runtime());
        res.clear();
        appendStmt(res, std::move(newStmt));
    }

    // Add cleanup merges at the end of the epoch
    appendStmt(res, generateCleanupMerges(sccOrdering));

    // Program translated!
    return mk<ram::Sequence>(std::move(res));
}

Own<ram::Statement> UnitTranslator::generateNonRecursiveRelation(const ast::Relation& rel) const {
    auto addProfiling = [](const ast::Relation& rel, const ast::Clause* clause, Own<ram::Statement> stmt) -> Own<ram::Statement> {
        if (Global::config().has("profile")) {
            const std::string& relationName = toString(rel.getQualifiedName());
            const auto& srcLocation = clause->getSrcLoc();
            const std::string clauseText = stringify(toString(*clause));
            const std::string logTimerStatement = LogStatement::tNonrecursiveRule(relationName, srcLocation, clauseText);
            return mk<ram::LogRelationTimer>(std::move(stmt), logTimerStatement,
                    getConcreteRelationName(rel.getQualifiedName()));
        }
        return stmt;
    };

    auto addDebugInfo = [](const ast::Clause* clause, Own<ram::Statement> stmt) -> Own<ram::Statement> {
        // Add debug info
        std::ostringstream ds;
        ds << toString(*clause) << "\nin file ";
        ds << clause->getSrcLoc();

        return mk<ram::DebugInfo>(std::move(stmt), ds.str());
    };

    VecOwn<ram::Statement> result;

    // Get relation names
    std::string mainRelation = getConcreteRelationName(rel.getQualifiedName());

    // Iterate over all non-recursive clauses that belong to the relation
    for (auto&& clause : context->getProgram()->getClauses(rel)) {
        // Skip recursive and subsumptive clauses
        if (context->isRecursiveClause(clause) || isA<ast::SubsumptiveClause>(clause)) {
            continue;
        }

        // Translate each diff version, where the diff_minus/diff_plus occurs in
        // different body atom positions in each diff version
        VecOwn<ram::Statement> clauseDiffVersions = translateNonRecursiveClauseDiffVersions(*clause);
        for (auto& clauseDiffVersion : clauseDiffVersions) {
            appendStmt(result, addDebugInfo(clause, addProfiling(rel, clause, std::move(clauseDiffVersion))));
        }
    }

    // Add logging for entire relation
    if (Global::config().has("profile")) {
        const std::string& relationName = toString(rel.getQualifiedName());
        const auto& srcLocation = rel.getSrcLoc();
        const std::string logSizeStatement = LogStatement::nNonrecursiveRelation(relationName, srcLocation);

        // Add timer if we did any work
        if (!result.empty()) {
            const std::string logTimerStatement =
                    LogStatement::tNonrecursiveRelation(relationName, srcLocation);
            auto newStmt = mk<ram::LogRelationTimer>(
                    mk<ram::Sequence>(std::move(result)), logTimerStatement, mainRelation);
            result.clear();
            appendStmt(result, std::move(newStmt));
        } else {
            // Add table size printer
            appendStmt(result, mk<ram::LogSize>(mainRelation, logSizeStatement));
        }
    }

    // TODO (DZ): More correctly, this section should go into
    // generateStratumPreamble, BUT, this also needs to apply after IO strata -
    // therefore this should be refactored into its own method?

    // Generate merges from diff_plus/diff_minus into main relation
    appendStmt(result, generateMergeRelations(&rel, getConcreteRelationName(rel.getQualifiedName()), getDiffMinusRelationName(rel.getQualifiedName())));
    appendStmt(result, generateMergeRelations(&rel, getConcreteRelationName(rel.getQualifiedName()), getDiffPlusRelationName(rel.getQualifiedName())));

    // Generate checked merges
    appendStmt(result, generateMergeRelationsActualDiff(&rel,
                getActualDiffMinusRelationName(rel.getQualifiedName()),
                getDiffMinusRelationName(rel.getQualifiedName()),
                getConcreteRelationName(rel.getQualifiedName()),
                -1));

    appendStmt(result, generateMergeRelationsActualDiff(&rel,
                getActualDiffPlusRelationName(rel.getQualifiedName()),
                getDiffPlusRelationName(rel.getQualifiedName()),
                getPrevRelationName(rel.getQualifiedName()),
                1));


    return mk<ram::Sequence>(std::move(result));
}

VecOwn<ram::Statement> UnitTranslator::translateNonRecursiveClauseDiffVersions(const ast::Clause& clause) const {
    // Generate diff versions
    VecOwn<ram::Statement> clauseDiffVersions;

    // for (std::size_t diffVersion = 0; diffVersion < ast::getBodyLiterals<ast::Atom>(clause).size(); diffVersion++) {
    appendStmt(clauseDiffVersions, context->translateNonRecursiveClause(clause, IncrementalDiffMinus));
    appendStmt(clauseDiffVersions, context->translateNonRecursiveClause(clause, IncrementalDiffPlus));
    // }

    return clauseDiffVersions;
}


VecOwn<ram::Statement> UnitTranslator::generateClauseVersions(
        const ast::Clause* clause, const std::set<const ast::Relation*>& scc) const {
    const auto& sccAtoms = getSccAtoms(clause, scc);

    // Create each version
    VecOwn<ram::Statement> clauseVersions;
    for (std::size_t version = 0; version < sccAtoms.size(); version++) {
        appendStmt(clauseVersions, context->translateRecursiveClause(*clause, scc, version, IncrementalDiffMinus));
        appendStmt(clauseVersions, context->translateRecursiveClause(*clause, scc, version, IncrementalDiffPlus));

        appendStmt(clauseVersions, context->translateRecursiveClause(*clause, scc, version, IncrementalUpdatedDiffMinus));
        appendStmt(clauseVersions, context->translateRecursiveClause(*clause, scc, version, IncrementalUpdatedDiffPlus));
    }

    // Check that the correct number of versions have been created
    if (clause->getExecutionPlan() != nullptr) {
        std::optional<std::size_t> maxVersion;
        for (const auto& cur : clause->getExecutionPlan()->getOrders()) {
            maxVersion = std::max(cur.first, maxVersion.value_or(cur.first));
        }
        assert(sccAtoms.size() > *maxVersion && "missing clause versions");
    }

    return clauseVersions;
}

Own<ram::Relation> UnitTranslator::createRamRelation(
        const ast::Relation* baseRelation, std::string ramRelationName) const {
    auto arity = baseRelation->getArity();
    // auto representation = baseRelation->getRepresentation();
    auto representation = RelationRepresentation::INCREMENTAL;

    // Add in base relation information
    std::vector<std::string> attributeNames;
    std::vector<std::string> attributeTypeQualifiers;
    for (const auto& attribute : baseRelation->getAttributes()) {
        attributeNames.push_back(attribute->getName());
        attributeTypeQualifiers.push_back(context->getAttributeTypeQualifier(attribute->getTypeName()));
    }

    // Add in provenance information
    attributeNames.push_back("@iteration");
    attributeTypeQualifiers.push_back("i:number");

    attributeNames.push_back("@count");
    attributeTypeQualifiers.push_back("i:number");

    return mk<ram::Relation>(
            ramRelationName, arity + 2, 2, attributeNames, attributeTypeQualifiers, representation);
}

Own<ram::Statement> UnitTranslator::generateStratumPreamble(const std::set<const ast::Relation*>& scc) const {
    VecOwn<ram::Statement> preamble;

    // Generate code for non-recursive rules
    for (const ast::Relation* rel : scc) {
        std::string deltaRelation = getDeltaRelationName(rel->getQualifiedName());
        std::string mainRelation = getConcreteRelationName(rel->getQualifiedName());
        appendStmt(preamble, generateNonRecursiveRelation(*rel));
    }

    // Generate non recursive delete sequences for subsumptive rules
    appendStmt(preamble, generateNonRecursiveDelete(scc));

    /*
    // Generate code for priming relation
    for (const ast::Relation* rel : scc) {
        std::string deltaRelation = getDeltaRelationName(rel->getQualifiedName());
        std::string mainRelation = getConcreteRelationName(rel->getQualifiedName());
        appendStmt(preamble, generateMergeRelations(rel, deltaRelation, mainRelation));
    }
    */
    return mk<ram::Sequence>(std::move(preamble));
}

Own<ram::Statement> UnitTranslator::generateStratumPostamble(
        const std::set<const ast::Relation*>& scc) const {
    VecOwn<ram::Statement> postamble;
    for (const ast::Relation* rel : scc) {
        // Drop temporary tables after recursion
        appendStmt(postamble, mk<ram::Clear>(getNewDiffPlusRelationName(rel->getQualifiedName())));
        appendStmt(postamble, mk<ram::Clear>(getNewDiffMinusRelationName(rel->getQualifiedName())));
        appendStmt(postamble, mk<ram::Clear>(getUpdatedDiffPlusRelationName(rel->getQualifiedName())));
        appendStmt(postamble, mk<ram::Clear>(getUpdatedDiffMinusRelationName(rel->getQualifiedName())));
    }
    return mk<ram::Sequence>(std::move(postamble));
}

Own<ram::Statement> UnitTranslator::generateStratumTableUpdates(const std::set<const ast::Relation*>& scc) const {
    VecOwn<ram::Statement> updateTable;

    for (const ast::Relation* rel : scc) {
        std::string mainRelation = getConcreteRelationName(rel->getQualifiedName());
        std::string prevRelation = getPrevRelationName(rel->getQualifiedName());

        std::string updatedMinusRelation = getUpdatedDiffMinusRelationName(rel->getQualifiedName());
        std::string updatedPlusRelation = getUpdatedDiffPlusRelationName(rel->getQualifiedName());

        std::string newDiffMinusRelation = getNewDiffMinusRelationName(rel->getQualifiedName());
        std::string newDiffPlusRelation = getNewDiffPlusRelationName(rel->getQualifiedName());

        std::string diffMinusRelation = getDiffMinusRelationName(rel->getQualifiedName());
        std::string diffPlusRelation = getDiffPlusRelationName(rel->getQualifiedName());

        std::string actualDiffMinusRelation = getActualDiffMinusRelationName(rel->getQualifiedName());
        std::string actualDiffPlusRelation = getActualDiffPlusRelationName(rel->getQualifiedName());

        /*
        // swap new and and delta relation and clear new relation afterwards (if not a subsumptive relation)
        Own<ram::Statement> updateRelTable;
        if (!context->hasSubsumptiveClause(rel->getQualifiedName())) {
            updateRelTable = mk<ram::Sequence>(generateMergeRelations(rel, mainRelation, newRelation),
                    mk<ram::Swap>(deltaRelation, newRelation), mk<ram::Clear>(newRelation));
        } else {
            updateRelTable = generateMergeRelations(rel, mainRelation, deltaRelation);
        }
        */

        VecOwn<ram::Statement> updateStmts;

        // Clear temp relations
        appendStmt(updateStmts, mk<ram::Clear>(updatedMinusRelation));
        appendStmt(updateStmts, mk<ram::Clear>(updatedPlusRelation));

        // Merge new_diff_minus/plus to store the current state of the diffs and the main relation
        appendStmt(updateStmts, generateMergeRelations(rel, diffMinusRelation, newDiffMinusRelation));
        appendStmt(updateStmts, generateMergeRelations(rel, diffPlusRelation, newDiffPlusRelation));
        appendStmt(updateStmts, generateMergeRelations(rel, mainRelation, newDiffMinusRelation));
        appendStmt(updateStmts, generateMergeRelations(rel, mainRelation, newDiffPlusRelation));

        // Generate correct actual_diff_minus/plus and updated_diff_minus/plus
        appendStmt(updateStmts, generateMergeRelationsActualDiff(rel, actualDiffMinusRelation, newDiffMinusRelation, mainRelation, -1));
        appendStmt(updateStmts, generateMergeRelationsActualDiffUpdated(rel,
                    actualDiffMinusRelation,
                    mainRelation,
                    updatedMinusRelation,
                    1));

        appendStmt(updateStmts, generateMergeRelationsActualDiff(rel, actualDiffPlusRelation, newDiffPlusRelation, prevRelation, 1));
        appendStmt(updateStmts, generateMergeRelationsActualDiffUpdated(rel,
                    actualDiffPlusRelation,
                    prevRelation,
                    updatedPlusRelation,
                    -1));

        appendStmt(updateStmts, mk<ram::Clear>(newDiffMinusRelation));
        appendStmt(updateStmts, mk<ram::Clear>(newDiffPlusRelation));

        Own<ram::Statement> updateRelTable = mk<ram::Sequence>(std::move(updateStmts));

        // Measure update time
        if (Global::config().has("profile")) {
            updateRelTable = mk<ram::LogRelationTimer>(std::move(updateRelTable),
                    LogStatement::cRecursiveRelation(toString(rel->getQualifiedName()), rel->getSrcLoc()),
                    mainRelation);
        }

        appendStmt(updateTable, std::move(updateRelTable));
    }
    return mk<ram::Sequence>(std::move(updateTable));

}

VecOwn<ram::Relation> UnitTranslator::createRamRelations(const std::vector<std::size_t>& sccOrdering) const {
    // Regular relations
    auto ramRelations = seminaive::UnitTranslator::createRamRelations(sccOrdering);

    // We need to also generate all the auxiliary relations:
    // - prev
    // - delta_prev
    // - new_prev
    //      - if we keep the normal relation as the updated one, the instead of diff_applied,
    //        we can have prev
    // - temp_diff_plus (updated_diff_plus)
    // - temp_diff_minus (updated_diff_minus)
    //      - check if we can simulate semantics of temp without having extra relations
    //        this might be slow, but do it as an initial step
    // - diff_plus
    // - diff_minus
    // - delta_diff_plus
    // - delta_diff_minus
    // - new_diff_plus
    // - new_diff_minus

    return ramRelations;
}

void UnitTranslator::addAuxiliaryArity(
        const ast::Relation* /* relation */, std::map<std::string, std::string>& directives) const {
    // directives.insert(std::make_pair("auxArity", "2"));
    directives.insert(std::make_pair("auxValues", "0,1"));
}

Own<ram::Statement> UnitTranslator::generateLoadRelation(const ast::Relation* /* relation */) const {
    // Don't load relations again during inc update
    return mk<ram::Sequence>();
}

Own<ram::Statement> UnitTranslator::generateClearExpiredRelations(
        const std::set<const ast::Relation*>& /* expiredRelations */) const {
    // Relations should be preserved if incremental is enabled
    return mk<ram::Sequence>();
}

/*
Own<ram::Statement> UnitTranslator::generateStratumTableUpdates(
        const std::set<const ast::Relation*>& scc) const {
    VecOwn<ram::Statement> updateTable;

    for (const ast::Relation* rel : scc) {
        // Copy @new into main relation, @delta := @new, and empty out @new
        std::string mainRelation = getConcreteRelationName(rel->getQualifiedName());
        std::string newRelation = getNewRelationName(rel->getQualifiedName());
        std::string deltaRelation = getDeltaRelationName(rel->getQualifiedName());

        // swap new and and delta relation and clear new relation afterwards (if not a subsumptive relation)
        Own<ram::Statement> updateRelTable;
        if (!context->hasSubsumptiveClause(rel->getQualifiedName())) {
            updateRelTable = mk<ram::Sequence>(mk<ram::Clear>(deltaRelation),
                    generateMergeRelationsWithFilter(rel, deltaRelation, newRelation, mainRelation),
                    generateMergeRelations(rel, mainRelation, newRelation),
                    mk<ram::Clear>(newRelation));

        }

        // Measure update time
        if (Global::config().has("profile")) {
            updateRelTable = mk<ram::LogRelationTimer>(std::move(updateRelTable),
                    LogStatement::cRecursiveRelation(toString(rel->getQualifiedName()), rel->getSrcLoc()),
                    newRelation);
        }

        appendStmt(updateTable, std::move(updateRelTable));
    }
    return mk<ram::Sequence>(std::move(updateTable));
}
*/

Own<ram::Statement> UnitTranslator::generateMergeRelations(
        const ast::Relation* rel, const std::string& destRelation, const std::string& srcRelation) const {
    VecOwn<ram::Expression> values;

    // Predicate - insert all values
    for (std::size_t i = 0; i < rel->getArity() + 2; i++) {
        values.push_back(mk<ram::TupleElement>(0, i));
    }

    auto insertion = mk<ram::Insert>(destRelation, std::move(values));
    auto stmt = mk<ram::Query>(mk<ram::Scan>(srcRelation, 0, std::move(insertion)));
    return stmt;
}

Own<ram::Statement> UnitTranslator::generateMergeRelationsWithFilter(const ast::Relation* rel,
        const std::string& destRelation, const std::string& srcRelation,
        const std::string& filterRelation) const {
    VecOwn<ram::Expression> values;
    VecOwn<ram::Expression> values2;

    // Predicate - insert all values
    for (std::size_t i = 0; i < rel->getArity() + 2; i++) {
        values.push_back(mk<ram::TupleElement>(0, i));
        if (i < rel->getArity()) {
            values2.push_back(mk<ram::TupleElement>(0, i));
        } else {
            values2.push_back(mk<ram::UndefValue>());
        }
    }
    auto insertion = mk<ram::Insert>(destRelation, std::move(values));
    auto filtered =
            mk<ram::Filter>(mk<ram::Negation>(mk<ram::ExistenceCheck>(filterRelation, std::move(values2))),
                    std::move(insertion));
    auto stmt = mk<ram::Query>(mk<ram::Scan>(srcRelation, 0, std::move(filtered)));
    return stmt;
}

Own<ram::Statement> UnitTranslator::generateMergeRelationsActualDiff(
        const ast::Relation* rel, const std::string& destRelation, const std::string& srcRelation,
        const std::string& checkRelation, int insertTupleCount) const {

    // For some relation R, this method generates a merge that is as follows:
    //
    // FOR t0 IN srcRelation:
    //   IF t0.iter = iternum():
    //     IF NOT EXISTS t1 IN checkRelation WHERE t1.0 = t0.0 AND t1.1 = t0.1 AND ... AND t1.iter <= iternum() AND t1.count > 0:
    //       INSERT t0.0, t0.1, ..., insertTupleCount INTO destRelation

    // Create insertion
    VecOwn<ram::Expression> values;

    for (std::size_t i = 0; i < rel->getArity() + 1; i++) {
        values.push_back(mk<ram::TupleElement>(0, i));
    }
    values.push_back(mk<ram::SignedConstant>(insertTupleCount));

    Own<ram::Operation> op = mk<ram::Insert>(destRelation, std::move(values));

    // Create filter for checking in checkRelation
    Own<ram::Condition> existenceCond;
    for (size_t i = 0; i < rel->getArity(); i++) {
        existenceCond = addConjunctiveTerm(std::move(existenceCond), mk<ram::Constraint>(
                    BinaryConstraintOp::EQ,
                    mk<ram::TupleElement>(0, i),
                    mk<ram::TupleElement>(1, i)));
    }

    existenceCond = addConjunctiveTerm(std::move(existenceCond), mk<ram::Constraint>(
                BinaryConstraintOp::LE,
                mk<ram::TupleElement>(1, rel->getArity()),
                mk<ram::IterationNumber>()));

    existenceCond = addConjunctiveTerm(std::move(existenceCond), mk<ram::Constraint>(
                BinaryConstraintOp::GT,
                mk<ram::TupleElement>(1, rel->getArity() + 1),
                mk<ram::SignedConstant>(0)));

    op = mk<ram::IfNotExists>(checkRelation, 1, std::move(existenceCond), std::move(op));

    // Create filter for iternum
    op = mk<ram::Filter>(mk<ram::Constraint>(
                BinaryConstraintOp::EQ,
                mk<ram::TupleElement>(0, rel->getArity()),
                mk<ram::IterationNumber>()),
            std::move(op));

    // Create outer scan
    auto stmt = mk<ram::Query>(mk<ram::Scan>(srcRelation, 0, std::move(op)));

    return stmt;
}

Own<ram::Statement> UnitTranslator::generateMergeRelationsActualDiffUpdated(
        const ast::Relation* rel, const std::string& toUpdateRelation,
        const std::string& checkRelation, const std::string& updatedRelation, int insertTupleCount) const {

    // For some relation R, this method generates a merge that is as follows:
    //
    // FOR t0 IN toUpdateRelation:
    //   IF t0.iter < iternum():
    //     FOR t1 IN checkRelation:
    //       IF t1.payload = t0.payload AND t1.iter = iternum() AND t1.count > 0:
    //         INSERT t0.payload, t0.iter, 0 INTO toUpdateRelation
    //         INSERT t0 INTO updatedRelation

    // Create insertion
    VecOwn<ram::Expression> toUpdateValues;
    VecOwn<ram::Expression> updatedValues;

    for (std::size_t i = 0; i < rel->getArity() + 1; i++) {
        toUpdateValues.push_back(mk<ram::TupleElement>(0, i));
    }
    toUpdateValues.push_back(mk<ram::SignedConstant>(insertTupleCount));

    for (std::size_t i = 0; i < rel->getArity(); i++) {
        updatedValues.push_back(mk<ram::TupleElement>(0, i));
    }
    updatedValues.push_back(mk<ram::IterationNumber>());
    updatedValues.push_back(mk<ram::SignedConstant>(1));

    Own<ram::Operation> op = mk<ram::OperationSequence>(
            mk<ram::Insert>(toUpdateRelation, std::move(toUpdateValues)),
            mk<ram::Insert>(updatedRelation, std::move(updatedValues)));

    // Create filter for checking in checkRelation
    Own<ram::Condition> existenceCond;
    for (size_t i = 0; i < rel->getArity(); i++) {
        existenceCond = addConjunctiveTerm(std::move(existenceCond), mk<ram::Constraint>(
                    BinaryConstraintOp::EQ,
                    mk<ram::TupleElement>(0, i),
                    mk<ram::TupleElement>(1, i)));
    }

    existenceCond = addConjunctiveTerm(std::move(existenceCond), mk<ram::Constraint>(
                BinaryConstraintOp::EQ,
                mk<ram::TupleElement>(1, rel->getArity()),
                mk<ram::IterationNumber>()));

    existenceCond = addConjunctiveTerm(std::move(existenceCond), mk<ram::Constraint>(
                BinaryConstraintOp::GT,
                mk<ram::TupleElement>(1, rel->getArity() + 1),
                mk<ram::SignedConstant>(0)));

    op = mk<ram::Filter>(std::move(existenceCond), std::move(op));

    // Make inner scan
    op = mk<ram::Scan>(checkRelation, 1, std::move(op));

    // Create filter for iternum
    Own<ram::Condition> toUpdateCond;
    toUpdateCond = addConjunctiveTerm(std::move(toUpdateCond), mk<ram::Constraint>(
            BinaryConstraintOp::LT,
            mk<ram::TupleElement>(0, rel->getArity()),
            mk<ram::IterationNumber>()));

    // Filter for count
    // TODO (DZ): this is a hack, but insertTupleCount < 0 indicates we are
    // dealing with diff_plus, so should check for positive count,
    // insertTupleCount > 0 indicates we are dealing with diff_minus, so
    // should check for negative count
    toUpdateCond = addConjunctiveTerm(std::move(toUpdateCond), mk<ram::Constraint>(
            ((insertTupleCount < 0) ? BinaryConstraintOp::GT : BinaryConstraintOp::LT),
            mk<ram::TupleElement>(0, rel->getArity() + 1),
            mk<ram::SignedConstant>(0)));


    op = mk<ram::Filter>(std::move(toUpdateCond), std::move(op));

    // Create outer scan
    auto stmt = mk<ram::Query>(mk<ram::Scan>(toUpdateRelation, 0, std::move(op)));

    return stmt;
}

Own<ram::Statement> UnitTranslator::generateStratumExitSequence(
        const std::set<const ast::Relation*>& scc) const {
    // Helper function to add a new term to a conjunctive condition
    auto addCondition = [&](Own<ram::Condition>& cond, Own<ram::Condition> term) {
        cond = (cond == nullptr) ? std::move(term) : mk<ram::Conjunction>(std::move(cond), std::move(term));
    };

    VecOwn<ram::Statement> exitConditions;

    // (1) if all relations in the scc are empty
    Own<ram::Condition> emptinessCheck;
    for (const ast::Relation* rel : scc) {
        addCondition(
                emptinessCheck, mk<ram::EmptinessCheck>(getNewDiffPlusRelationName(rel->getQualifiedName())));
        addCondition(
                emptinessCheck, mk<ram::EmptinessCheck>(getNewDiffMinusRelationName(rel->getQualifiedName())));
    }
    appendStmt(exitConditions, mk<ram::Exit>(std::move(emptinessCheck)));

    // (2) if the size limit has been reached for any limitsize relations
    for (const ast::Relation* rel : scc) {
        if (context->hasSizeLimit(rel)) {
            Own<ram::Condition> limit = mk<ram::Constraint>(BinaryConstraintOp::GE,
                    mk<ram::RelationSize>(getConcreteRelationName(rel->getQualifiedName())),
                    mk<ram::SignedConstant>(context->getSizeLimit(rel)));
            appendStmt(exitConditions, mk<ram::Exit>(std::move(limit)));
        }
    }

    // TODO: (3) if we haven't reached the same iteration number as in the previous epoch

    return mk<ram::Sequence>(std::move(exitConditions));
}


Own<ram::Statement> UnitTranslator::generateCleanupMerges(const std::vector<std::size_t>& sccOrdering) const {
    VecOwn<ram::Statement> cleanupSequence;
    for (const auto& scc : sccOrdering) {
        for (const auto& rel : context->getRelationsInSCC(scc)) {
            appendStmt(cleanupSequence, generateMergeRelations(rel, getPrevRelationName(rel->getQualifiedName()), getDiffMinusRelationName(rel->getQualifiedName())));
            appendStmt(cleanupSequence, generateMergeRelations(rel, getPrevRelationName(rel->getQualifiedName()), getDiffPlusRelationName(rel->getQualifiedName())));

            appendStmt(cleanupSequence, mk<ram::Clear>(getDiffMinusRelationName(rel->getQualifiedName())));
            appendStmt(cleanupSequence, mk<ram::Clear>(getDiffPlusRelationName(rel->getQualifiedName())));
            appendStmt(cleanupSequence, mk<ram::Clear>(getActualDiffMinusRelationName(rel->getQualifiedName())));
            appendStmt(cleanupSequence, mk<ram::Clear>(getActualDiffPlusRelationName(rel->getQualifiedName())));
        }
    }
    return mk<ram::Sequence>(std::move(cleanupSequence));
}

Own<ram::SubroutineReturn> UnitTranslator::makeRamReturnTrue() const {
    VecOwn<ram::Expression> returnTrue;
    returnTrue.push_back(mk<ram::SignedConstant>(1));
    return mk<ram::SubroutineReturn>(std::move(returnTrue));
}

Own<ram::SubroutineReturn> UnitTranslator::makeRamReturnFalse() const {
    VecOwn<ram::Expression> returnFalse;
    returnFalse.push_back(mk<ram::SignedConstant>(0));
    return mk<ram::SubroutineReturn>(std::move(returnFalse));
}

Own<ram::Sequence> UnitTranslator::makeIfStatement(
        Own<ram::Condition> condition, Own<ram::Operation> trueOp, Own<ram::Operation> falseOp) const {
    auto negatedCondition = mk<ram::Negation>(clone(condition));

    auto trueBranch = mk<ram::Query>(mk<ram::Filter>(std::move(condition), std::move(trueOp)));
    auto falseBranch = mk<ram::Query>(mk<ram::Filter>(std::move(negatedCondition), std::move(falseOp)));

    return mk<ram::Sequence>(std::move(trueBranch), std::move(falseBranch));
}

std::map<std::string, Own<ram::Statement>>& UnitTranslator::getRamSubroutines() {
    /*
    std::map<std::string, ram::Statement*> res;

    for (const auto& sub : updateRamSubroutines) {
        res.insert(std::make_pair(sub.first, sub.second.get()));
    }
    */

    return updateRamSubroutines;
}

}  // namespace souffle::ast2ram::incremental::update
