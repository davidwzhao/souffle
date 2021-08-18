/**
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Synthesiser.cpp
 *
 * Implementation of the C++ synthesiser for RAM programs.
 *
 ***********************************************************************/

#include "Synthesiser.h"
#include "BinaryConstraintOps.h"
#include "FunctorOps.h"
#include "Global.h"
#include "IODirectives.h"
#include "RamCondition.h"
#include "RamExpression.h"
#include "RamIndexAnalysis.h"
#include "RamNode.h"
#include "RamOperation.h"
#include "RamProgram.h"
#include "RamRelation.h"
#include "RamTranslationUnit.h"
#include "RamVisitor.h"
#include "RelationRepresentation.h"
#include "SymbolTable.h"
#include "SynthesiserRelation.h"
#include "Util.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <sstream>
#include <typeinfo>
#include <utility>
#include <vector>

namespace souffle {

/** Lookup frequency counter */
unsigned Synthesiser::lookupFreqIdx(const std::string& txt) {
    static unsigned ctr;
    auto pos = idxMap.find(txt);
    if (pos == idxMap.end()) {
        return idxMap[txt] = ctr++;
    } else {
        return idxMap[txt];
    }
}

/** Lookup frequency counter */
size_t Synthesiser::lookupReadIdx(const std::string& txt) {
    std::string modifiedTxt = txt;
    for (auto& cur : modifiedTxt) {
        if (cur == '-') {
            cur = '.';
        }
    }
    static unsigned counter;
    auto pos = neIdxMap.find(modifiedTxt);
    if (pos == neIdxMap.end()) {
        return neIdxMap[modifiedTxt] = counter++;
    } else {
        return neIdxMap[modifiedTxt];
    }
}

/** Convert RAM identifier */
const std::string Synthesiser::convertRamIdent(const std::string& name) {
    auto it = identifiers.find(name);
    if (it != identifiers.end()) {
        return it->second;
    }
    // strip leading numbers
    unsigned int i;
    for (i = 0; i < name.length(); ++i) {
        if (isalnum(name.at(i)) || name.at(i) == '_') {
            break;
        }
    }
    std::string id;
    for (auto ch : std::to_string(identifiers.size() + 1) + '_' + name.substr(i)) {
        // alphanumeric characters are allowed
        if (isalnum(ch)) {
            id += ch;
        }
        // all other characters are replaced by an underscore, except when
        // the previous character was an underscore as double underscores
        // in identifiers are reserved by the standard
        else if (id.empty() || id.back() != '_') {
            id += '_';
        }
    }
    // most compilers have a limit of 2048 characters (if they have a limit at all) for
    // identifiers; we use half of that for safety
    id = id.substr(0, 1024);
    identifiers.insert(std::make_pair(name, id));
    return id;
}

/** check whether indexes are disabled */
bool Synthesiser::areIndexesDisabled() {
    bool flag = std::getenv("SOUFFLE_USE_NO_INDEX");
    static bool first = true;
    if (first && flag) {
        std::cout << "WARNING: indexes are ignored!\n";
        first = false;
    }
    return flag;
}

/** Get relation name */
const std::string Synthesiser::getRelationName(const RamRelation& rel) {
    return "rel_" + convertRamIdent(rel.getName());
}

/** Get relation name via string */
const std::string Synthesiser::getRelationName(const std::string& relName) {
    return "rel_" + convertRamIdent(relName);
}

/** Get context name */
const std::string Synthesiser::getOpContextName(const RamRelation& rel) {
    return getRelationName(rel) + "_op_ctxt";
}

/** Get relation type struct */
void Synthesiser::generateRelationTypeStruct(
        std::ostream& out, std::unique_ptr<SynthesiserRelation> relationType) {
    // If this type has been generated already, use the cached version
    if (typeCache.find(relationType->getTypeName()) != typeCache.end()) {
        return;
    }
    typeCache.insert(relationType->getTypeName());

    // Generate the type struct for the relation
    relationType->generateTypeStruct(out);
}

/* Convert SearchColums to a template index */
std::string Synthesiser::toIndex(SearchSignature key) {
    std::stringstream tmp;
    tmp << "<";
    int i = 0;
    while (key != 0) {
        if (key % 2) {
            tmp << i;
            if (key > 1) {
                tmp << ",";
            }
        }
        key >>= 1;
        i++;
    }

    tmp << ">";
    return tmp.str();
}

/** Get referenced relations */
std::set<const RamRelation*> Synthesiser::getReferencedRelations(const RamOperation& op) {
    std::set<const RamRelation*> res;
    visitDepthFirst(op, [&](const RamNode& node) {
        if (auto scan = dynamic_cast<const RamRelationOperation*>(&node)) {
            res.insert(&scan->getRelation());
        } else if (auto agg = dynamic_cast<const RamAggregate*>(&node)) {
            res.insert(&agg->getRelation());
        } else if (auto exists = dynamic_cast<const RamExistenceCheck*>(&node)) {
            res.insert(&exists->getRelation());
        } else if (auto posExists = dynamic_cast<const RamPositiveExistenceCheck*>(&node)) {
            res.insert(&posExists->getRelation());
        } else if (auto subsumptionExists = dynamic_cast<const RamSubsumptionExistenceCheck*>(&node)) {
            res.insert(&subsumptionExists->getRelation());
        } else if (auto project = dynamic_cast<const RamProject*>(&node)) {
            res.insert(&project->getRelation());
        }
    });
    return res;
}

void Synthesiser::emitCode(std::ostream& out, const RamStatement& stmt) {
    class CodeEmitter : public RamVisitor<void, std::ostream&> {
    private:
        Synthesiser& synthesiser;
        RamIndexAnalysis* isa;

// macros to add comments to generated code for debugging
#ifndef PRINT_BEGIN_COMMENT
#define PRINT_BEGIN_COMMENT(os)                                                  \
    if (Global::config().has("debug-report") || Global::config().has("verbose")) \
    os << "/* BEGIN " << __FUNCTION__ << " @" << __FILE__ << ":" << __LINE__ << " */\n"
#endif

#ifndef PRINT_END_COMMENT
#define PRINT_END_COMMENT(os)                                                    \
    if (Global::config().has("debug-report") || Global::config().has("verbose")) \
    os << "/* END " << __FUNCTION__ << " @" << __FILE__ << ":" << __LINE__ << " */\n"
#endif

        std::function<void(std::ostream&, const RamNode*)> rec;
        std::ostringstream preamble;
        bool preambleIssued = false;

    public:
        CodeEmitter(Synthesiser& syn)
                : synthesiser(syn), isa(syn.getTranslationUnit().getAnalysis<RamIndexAnalysis>()) {
            rec = [&](std::ostream& out, const RamNode* node) { this->visit(*node, out); };
        }

        // -- relation statements --

        void visitCreate(const RamCreate& /*create*/, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            PRINT_END_COMMENT(out);
        }

        void visitFact(const RamFact& fact, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << synthesiser.getRelationName(fact.getRelation()) << "->"
                << "insert(" << join(fact.getValues(), ",", rec) << ");\n";
            PRINT_END_COMMENT(out);
        }

        void visitLoad(const RamLoad& load, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "if (performIO) {\n";
            out << "auto ioStart = std::chrono::high_resolution_clock::now();\n";
            std::vector<bool> symbolMask;
            for (auto& cur : load.getRelation().getAttributeTypeQualifiers()) {
                symbolMask.push_back(cur[0] == 's');
            }
            // get some table details
            for (IODirectives ioDirectives : load.getIODirectives()) {
                out << "try {";
                out << "std::map<std::string, std::string> directiveMap(";
                out << ioDirectives << ");\n";
                out << R"_(if (!inputDirectory.empty() && directiveMap["IO"] == "file" && )_";
                out << "directiveMap[\"filename\"].front() != '/') {";
                out << R"_(directiveMap["filename"] = inputDirectory + "/" + directiveMap["filename"];)_";
                out << "}\n";
                out << "IODirectives ioDirectives(directiveMap);\n";
                out << "IOSystem::getInstance().getReader(";
                out << "std::vector<bool>({" << join(symbolMask) << "})";
                out << ", symTable, ioDirectives";
                out << ", " << (Global::config().has("incremental") ? "true" : "false");
                out << ", " << load.getRelation().getNumberOfHeights();
                out << ")->readAll(*" << synthesiser.getRelationName(load.getRelation());
                out << ");\n";
                out << "} catch (std::exception& e) {std::cerr << \"Error loading data: \" << e.what() << "
                       "'\\n';}\n";
            }
            out << "auto ioEnd = std::chrono::high_resolution_clock::now();\n";
            out << "ioTime += std::chrono::duration_cast<std::chrono::microseconds>(ioEnd - ioStart);\n";
            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitStore(const RamStore& store, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "if (performIO) {\n";
            std::vector<bool> symbolMask;
            for (auto& cur : store.getRelation().getAttributeTypeQualifiers()) {
                symbolMask.push_back(cur[0] == 's');
            }
            out << "auto ioStart = std::chrono::high_resolution_clock::now();\n";
            for (IODirectives ioDirectives : store.getIODirectives()) {
                out << "try {";
                out << "std::map<std::string, std::string> directiveMap(" << ioDirectives << ");\n";
                out << R"_(if (!outputDirectory.empty() && directiveMap["IO"] == "file" && )_";
                out << "directiveMap[\"filename\"].front() != '/') {";
                out << R"_(directiveMap["filename"] = outputDirectory + "/" + directiveMap["filename"];)_";
                out << "}\n";
                out << "IODirectives ioDirectives(directiveMap);\n";
                out << "IOSystem::getInstance().getWriter(";
                out << "std::vector<bool>({" << join(symbolMask) << "})";
                out << ", symTable, ioDirectives";
                out << ", " << (Global::config().has("incremental") ? "true" : "false");
                out << ", " << store.getRelation().getNumberOfHeights();
                out << ")->writeAll(*" << synthesiser.getRelationName(store.getRelation()) << ");\n";
                out << "} catch (std::exception& e) {std::cerr << e.what();exit(1);}\n";
            }
            out << "auto ioEnd = std::chrono::high_resolution_clock::now();\n";
            out << "ioTime += std::chrono::duration_cast<std::chrono::microseconds>(ioEnd - ioStart);\n";
            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitQuery(const RamQuery& query, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);

            // split terms of conditions of outer filter operation
            // into terms that require a context and terms that
            // do not require a context
            const RamOperation* next = &query.getOperation();
            std::vector<std::unique_ptr<RamCondition>> requireCtx;
            std::vector<std::unique_ptr<RamCondition>> freeOfCtx;
            if (const auto* filter = dynamic_cast<const RamFilter*>(&query.getOperation())) {
                next = &filter->getOperation();
                // Check terms of outer filter operation whether they can be pushed before
                // the context-generation for speed imrovements
                auto conditions = toConjunctionList(&filter->getCondition());
                for (auto const& cur : conditions) {
                    bool needContext = false;
                    visitDepthFirst(*cur, [&](const RamExistenceCheck& exists) { needContext = true; });
                    visitDepthFirst(*cur, [&](const RamSubsumptionExistenceCheck& exists) { needContext = true; });
                    visitDepthFirst(*cur, [&](const RamPositiveExistenceCheck& exists) { needContext = true; });
                    if (needContext) {
                        requireCtx.push_back(std::unique_ptr<RamCondition>(cur->clone()));
                    } else {
                        freeOfCtx.push_back(std::unique_ptr<RamCondition>(cur->clone()));
                    }
                }
                // discharge conditions that do not require a context
                if (freeOfCtx.size() > 0) {
                    out << "if(";
                    visit(*toCondition(toConstPtrVector(freeOfCtx)), out);
                    out << ") {\n";
                }
            }

            // outline each search operation to improve compilation time
#ifdef __clang__
#if __clang_major > 3
            out << "[&]()";
#endif
#else
            out << "[&]()";
#endif
            // enclose operation in its own scope
            out << "{\n";

            // check whether loop nest can be parallelized
            bool isParallel = false;
            visitDepthFirst(*next, [&](const RamAbstractParallel& node) { isParallel = true; });

            // reset preamble
            preamble.str("");
            preamble.clear();
            preambleIssued = false;

            // create operation contexts for this operation
            for (const RamRelation* rel : synthesiser.getReferencedRelations(query.getOperation())) {
                preamble << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(*rel);
                preamble << "," << synthesiser.getRelationName(*rel);
                preamble << "->createContext());\n";
            }

            // discharge conditions that require a context
            if (isParallel) {
                if (requireCtx.size() > 0) {
                    preamble << "if(";
                    visit(*toCondition(toConstPtrVector(requireCtx)), preamble);
                    preamble << ") {\n";
                    visit(*next, out);
                    out << "}\n";
                } else {
                    visit(*next, out);
                }
            } else {
                out << preamble.str();
                if (requireCtx.size() > 0) {
                    out << "if(";
                    visit(*toCondition(toConstPtrVector(requireCtx)), out);
                    out << ") {\n";
                    visit(*next, out);
                    out << "}\n";
                } else {
                    visit(*next, out);
                }
            }

            if (isParallel) {
                out << "PARALLEL_END;\n";  // end parallel
            }

            out << "}\n";
#ifdef __clang__
#if __clang_major > 3
            out << "();";  // call lambda
#endif
#else
            out << "();";  // call lambda
#endif
            if (freeOfCtx.size() > 0) {
                out << "}\n";
            }

            PRINT_END_COMMENT(out);
        }

        void visitMerge(const RamMerge& merge, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            if (merge.getTargetRelation().getRepresentation() == RelationRepresentation::EQREL) {
                out << synthesiser.getRelationName(merge.getSourceRelation()) << "->"
                    << "extend("
                    << "*" << synthesiser.getRelationName(merge.getTargetRelation()) << ");\n";
            }
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->"
                << "insertAll("
                << "*" << synthesiser.getRelationName(merge.getSourceRelation()) << ");\n";
            PRINT_END_COMMENT(out);
        }

        void visitRelationLoad(const RamRelationLoad& merge, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            /*
            if (merge.getTargetRelation().getRepresentation() == RelationRepresentation::EQREL) {
                out << synthesiser.getRelationName(merge.getSourceRelation()) << "->"
                    << "extend("
                    << "*" << synthesiser.getRelationName(merge.getTargetRelation()) << ");\n";
            }
            */

            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->"
                << "relationLoad("
                << "*" << synthesiser.getRelationName(merge.getSourceRelation()) << ");\n";
            PRINT_END_COMMENT(out);
        }

        void visitPositiveMerge(const RamPositiveMerge& merge, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            size_t arity = merge.getTargetRelation().getArity();
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getSourceRelation()) + ")";

            int searchSignature = isa->getSearchSignature(&merge);

            out << "{ auto currentIteration = " << synthesiser.getRelationName(merge.getSourceRelation()) << "->"
                << "equalRange";
            out << "_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";

            // iteration should find all tuples
            for (size_t i = 0; i < arity - 3; i++) {
                out << "0";
                out << ",";
            }

            // but only in the current iteration
            out << "iter,0,0";

            out << "}});\n"; //  << ctxName << ");\n";


            out << "for (auto& tup : currentIteration) {\n";
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tup);\n";

            out << "} }\n";

            PRINT_END_COMMENT(out);
        }

        void visitUpdateMerge(const RamUpdateMerge& merge, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            size_t arity = merge.getTargetRelation().getArity();
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getTargetRelation()) + ")";

            int searchSignature = isa->getSearchSignature(&merge);

            out << "{\n";

            out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getTargetRelation()) << "," << synthesiser.getRelationName(merge.getTargetRelation()) << "->createContext());\n";

            out << "for (const auto& tup : *" << synthesiser.getRelationName(merge.getSourceRelation()) << ") {\n";
            out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getTargetRelation()) << "->equalRange_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "tup[" << i << "]";
                out << ",";
            }

            // extra 0s for incremental annotations
            out << "0,0";
            out << "}}, " << ctxName << ");\n";

            out << "for (const auto& existingTup : existenceCheck) {\n";
            out << "if (existingTup[" << arity - 2 << "] > tup[" << arity - 2 << "]) {\n";
            out << "auto updateTuple = existingTup;\n";
            out << "updateTuple[" << arity - 1 << "] = 0;\n";
            // out << "updateTuple[" << arity - 2 << "] = 0;\n";

            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(updateTuple," << ctxName << ");\n";
            out << "}\n";

            out << "}\n"; // end of for existingTup

            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tup," << ctxName << ");\n";

            out << "}\n"; // end of for tup

            out << "}\n"; // end of inner context

            PRINT_END_COMMENT(out);
        }

        void visitExistingMerge(const RamExistingMerge& merge, std::ostream& out) override {
            // ExistingMerge works as follows:
            // ExistingMerge(A, B, C):
            //   FOR tuple in B:
            //     IF (tuple.iteration == iter - 1 || (iter == 0 && tuple.iteration == 0)):
            //       INSERT tuple INTO A
            //     ELSE IF (tuple in C) :
            //       INSERT tuple INTO A

            PRINT_BEGIN_COMMENT(out);
            size_t arity = merge.getTargetRelation().getArity();
            auto existingCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getExistingRelation()) + ")";
            auto targetCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getTargetRelation()) + ")";

            out << "{\n";
            out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getExistingRelation()) << "," << synthesiser.getRelationName(merge.getExistingRelation()) << "->createContext());\n";
            out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getTargetRelation()) << "," << synthesiser.getRelationName(merge.getTargetRelation()) << "->createContext());\n";

            // this is a bit of a mess, should integrate into search signatures
            int searchSignature = isa->getSearchSignature(&merge);

            out << "for (auto& tup : *" << synthesiser.getRelationName(merge.getSourceRelation()) << ") {\n";

            out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getExistingRelation()) << "->"
                << "equalRange";
            // out << synthesiser.toIndex(ne.getSearchSignature());
            out << "_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 3; i++) {
                out << "tup[" << i << "]";
                out << ",";
            }

            // extra 0s for incremental annotations
            out << "0,0,0";

            out << "}}, " << existingCtxName << ");\n";

            out << "if (!existenceCheck.empty() && (*existenceCheck.begin())[" << arity - 3 << "] != iter) {\n";
            out << "continue;\n";
            out << "}\n";

            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tup, " << targetCtxName << ");\n";


            

            /*
            // out << "if ((iter == 0 && tup[" << arity - 3 << "] == 0) || tup[" << arity - 3 << "] == iter-1) {\n";
            out << "if (tup[" << arity - 3 << "] == iter) {\n";
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tup);\n";
            out << "}\n";

            // else, check existence in ExistingRelation
            out << "else {\n";

            // this is a bit of a mess, should integrate into search signatures
            int searchSignature = isa->getSearchSignature(&merge);

            out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getExistingRelation()) << "->"
                << "equalRange";
            // out << synthesiser.toIndex(ne.getSearchSignature());
            out << "_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 3; i++) {
                out << "tup[" << i << "]";
                out << ",";
            }

            // extra 0s for incremental annotations
            out << "0,0,0";

            out << "}});\n"; //  << ctxName << ");\n";

            out << "if (!existenceCheck.empty()) {\n";
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tup);\n";
            out << "}\n";

            out << "}\n";
            */

            out << "}\n";

            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitSemiMerge(const RamSemiMerge& merge, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            size_t arity = merge.getTargetRelation().getArity();

            // this is a bit of a mess, should integrate into search signatures
            int searchSignature = isa->getSearchSignature(&merge);

            auto sourceCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getSourceRelation()) + ")";
            auto restrictionCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getRestrictionRelation()) + ")";
            auto targetCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getTargetRelation()) + ")";
            std::string updateCtxName = "";
            if (merge.isRecursive()) {
                updateCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getUpdateRelation()) + ")";
            }

            out << "{\n";
            out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getRestrictionRelation()) << "," << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->createContext());\n";
            if (synthesiser.getOpContextName(merge.getRestrictionRelation()) != synthesiser.getOpContextName(merge.getTargetRelation())) {
                out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getTargetRelation()) << "," << synthesiser.getRelationName(merge.getTargetRelation()) << "->createContext());\n";
            }
            if (synthesiser.getOpContextName(merge.getSourceRelation()) != synthesiser.getOpContextName(merge.getTargetRelation())) {
                out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getSourceRelation()) << "," << synthesiser.getRelationName(merge.getSourceRelation()) << "->createContext());\n";
            }
            if (merge.isRecursive()) {
                out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getUpdateRelation()) << "," << synthesiser.getRelationName(merge.getUpdateRelation()) << "->createContext());\n";
            }

            out << "auto deltaSource = " << synthesiser.getRelationName(merge.getSourceRelation()) << "->equalRange_" << (1 << (arity - 2));
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "0";
                out << ",";
            }
            out << "iter,0";
            out << "}}, " << sourceCtxName << ");\n";
            out << "for (const auto& tup : deltaSource) {\n";

            // for each tup in source (diff_plus/diff_minus),
            //   if tup doesn't exist in restriction,
            //     insert tup into target

            out << "auto restrictionExistenceCheck = " << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->equalRange_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "tup[" << i <<  "]";
                out << ",";
            }
            out << "0,0";
            out << "}}, " << restrictionCtxName << ");\n";

            // check if tup exists in restriction
            out << "bool insert = true;\n";
            out << "for (const auto& t : restrictionExistenceCheck) {\n";
            out << "if (t[" << arity - 2 << "] <= tup[" << arity - 2 << "] && t[" << arity - 1 << "] > 0) {\n";
            out << "insert = false;\n";
            out << "break;\n";
            out << "}\n";
            out << "}\n";

            // if insert, then insert with either -1 or 1
            out << "if (insert) {\n";
            out << "auto tuple = tup;\n";
            out << "tuple[" << arity - 1 << "] = tup[" << arity - 1 << "] < 0 ? -1 : 1;\n";
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tuple, " << targetCtxName << ");\n";
            out << "}\n";

            out << "}\n";

            out << "if (iter > 0) {\n";

            // second phase of merge
            // for each tup in delta restriction,
            //   if tup is in the source,
            //     this is not a 'true' insert/delete so update its count to 0

            out << "if (" << synthesiser.getRelationName(merge.getTargetRelation()) << "->approx_size() < " << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->approx_size(iter)) {\n";

            // use target relation as outer loop
            out << "for (const auto& tup : *" << synthesiser.getRelationName(merge.getTargetRelation()) << ") {\n";
            out << "if (tup[" << arity - 2 << "] == iter || tup[" << arity - 1 << "] == 0) continue;\n";

            // check existence in delta
            out << "auto deltaExistenceCheck = " << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->equalRange_" << searchSignature + (1 << (arity - 2));
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "tup[" << i <<  "]";
                out << ",";
            }
            out << "iter,0";
            out << "}}, " << restrictionCtxName << ");\n";

            out << "if (deltaExistenceCheck.empty()) continue;\n";
            out << "if ((*deltaExistenceCheck.begin())[" << arity - 1 << "] > 0) {\n";
            out << "auto tuple = tup;\n";
            out << "tuple[" << arity - 1 << "] = tup[" << arity - 1 << "] == -1 ? 1 : -1;\n";
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tuple, " << targetCtxName << ");\n";
            if (merge.isRecursive()) {
                out << "auto tupleUpdate = tup;\n";
                out << "tupleUpdate[" << arity - 2 << "] = iter;\n";
                out << "tupleUpdate[" << arity - 1 << "] = 1;\n";
                out << synthesiser.getRelationName(merge.getUpdateRelation()) << "->insert(tupleUpdate, " << updateCtxName << ");\n";
            }
            out << "}\n";
            out << "}\n";

            out << "} else {\n";
            // use deltaRestriction as outer loop
            out << "auto deltaRestriction = " << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->equalRange_" << (1 << (arity - 2));
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "0";
                out << ",";
            }
            out << "iter,0";
            out << "}}, " << restrictionCtxName << ");\n";


            out << "for (const auto& tup : deltaRestriction) {\n";
            out << "if (tup[" << arity - 1 << "] <= 0) {\n";
            out << "continue;\n";
            out << "}\n";
            out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getTargetRelation()) << "->"
                << "equalRange";
            // out << synthesiser.toIndex(ne.getSearchSignature());
            out << "_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "tup[" << i << "]";
                out << ",";
            }
            out << "0,0";
            out << "}}, " << targetCtxName << ");\n";

            out << "for (const auto& t : existenceCheck) {\n";
            out << "if (t[" << arity - 2 << "] == iter || t[" << arity - 1 << "] == 0) continue;\n";
            out << "auto tuple = t;\n";
            out << "tuple[" << arity - 1 << "] = t[" << arity - 1 << "] == -1 ? 1 : -1;\n";
            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tuple, " << targetCtxName << ");\n";
            if (merge.isRecursive()) {
                out << "auto tupleUpdate = t;\n";
                out << "tupleUpdate[" << arity - 2 << "] = iter;\n";
                out << "tupleUpdate[" << arity - 1 << "] = 1;\n";
                out << synthesiser.getRelationName(merge.getUpdateRelation()) << "->insert(tupleUpdate, " << updateCtxName << ");\n";
            }
            out << "}\n";
            out << "}\n";

            out << "}\n";

            out << "}\n";

            out << "}\n";






            /*
            out << "auto deltaExistenceCheck = " << synthesiser.getRelationName(merge.getSourceRelation()) << "->equalRange_" << (1 << arity - 2);
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 2; i++) {
                out << "0";
                out << ",";
            }
            out << "iter,0";
            out << "}}, " << sourceCtxName << ");\n";

            out << "for (auto& tup : deltaExistenceCheck) {\n";

            // check if tuple is in lower iteration in existing relation
            out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->"
                << "equalRange";
            // out << synthesiser.toIndex(ne.getSearchSignature());
            out << "_" << searchSignature;
            out << "(Tuple<RamDomain," << arity << ">{{";
            for (size_t i = 0; i < arity - 1; i++) {
                out << "tup[" << i << "]";
                out << ",";
            }

            // extra 0s for incremental annotations
            out << "0";

            out << "}}, " << restrictionCtxName << ");\n";
            out << "if (!existenceCheck.empty()) {\n";

            out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(*(existenceCheck.begin()), " << targetCtxName << ");\n";
            out << "}\n";

            out << "}\n";
            out << "}\n";
            */


            /*
            if (!merge.isSourceOuter()) {
                auto sourceCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getSourceRelation()) + ")";
                auto targetCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getTargetRelation()) + ")";
                out << "{\n";
                // if (synthesiser.contexts.find(synthesiser.getOpContextName(merge.getSourceRelation())) == synthesiser.contexts.end()) {
                    out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getSourceRelation()) << "," << synthesiser.getRelationName(merge.getSourceRelation()) << "->createContext());\n";
                    out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getTargetRelation()) << "," << synthesiser.getRelationName(merge.getTargetRelation()) << "->createContext());\n";
                    // synthesiser.contexts.insert(synthesiser.getOpContextName(merge.getSourceRelation()));
                // }
                out << "for (auto& tup : *" << synthesiser.getRelationName(merge.getRestrictionRelation()) << ") {\n";

                // TODO: enable generic conditions in the SemiMerge operation, this is temporarily just to get it to work
                // we want to only perform the semimerge if the tuple is in the current iteration
                out << "if (tup[" << arity - 3 << "] != iter) continue;\n";

                out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getSourceRelation()) << "->"
                    << "equalRange";
                // out << synthesiser.toIndex(ne.getSearchSignature());
                out << "_" << searchSignature;
                out << "(Tuple<RamDomain," << arity << ">{{";
                for (size_t i = 0; i < arity - 3; i++) {
                    out << "tup[" << i << "]";
                    out << ",";
                }

                // extra 0s for incremental annotations
                out << "0,0,0";

                out << "}}, " << sourceCtxName << ");\n";

                out << "if (existenceCheck.empty()) continue;\n";
                out << "for (auto& sourceTup : existenceCheck) {\n";
                out << "if (sourceTup[" << arity - 3 << "] != tup[" << arity - 3 << "]) continue;\n";
                out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(sourceTup, " << targetCtxName << ");\n";
                // out << "continue;\n";
                // out << "}\n";
                out << "}\n";

                out << "}\n";

                out << "}\n";
            } else {
                auto sourceCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getRestrictionRelation()) + ")";
                auto targetCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(merge.getTargetRelation()) + ")";
                out << "{\n";
                // if (synthesiser.contexts.find(synthesiser.getOpContextName(merge.getRestrictionRelation())) == synthesiser.contexts.end()) {
                    out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getRestrictionRelation()) << "," << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->createContext());\n";
                    out << "CREATE_OP_CONTEXT(" << synthesiser.getOpContextName(merge.getTargetRelation()) << "," << synthesiser.getRelationName(merge.getTargetRelation()) << "->createContext());\n";
                    // synthesiser.contexts.insert(synthesiser.getOpContextName(merge.getRestrictionRelation()));
                // }
                out << "for (auto& tup : *" << synthesiser.getRelationName(merge.getSourceRelation()) << ") {\n";

                // TODO: enable generic conditions in the SemiMerge operation, this is temporarily just to get it to work
                // we want to only perform the semimerge if the tuple is in the current iteration
                out << "if (tup[" << arity - 3 << "] != iter) continue;\n";

                out << "auto existenceCheck = " << synthesiser.getRelationName(merge.getRestrictionRelation()) << "->"
                    << "equalRange";
                // out << synthesiser.toIndex(ne.getSearchSignature());
                out << "_" << searchSignature;
                out << "(Tuple<RamDomain," << arity << ">{{";
                for (size_t i = 0; i < arity - 3; i++) {
                    out << "tup[" << i << "]";
                    out << ",";
                }

                // extra 0s for incremental annotations
                out << "0,0,0";

                out << "}}, " << sourceCtxName << ");\n";

                out << "if (existenceCheck.empty()) continue;\n";
                out << "else {\n";
                out << "for (auto& restrictionTup : existenceCheck) {\n";
                out << "if (restrictionTup[" << arity - 3 << "] == tup[" << arity - 3 << "]) {\n";
                out << synthesiser.getRelationName(merge.getTargetRelation()) << "->insert(tup, " << targetCtxName << ");\n";
                out << "break;\n";
                out << "}\n";
                out << "}\n";
                out << "}\n";
                out << "}\n";

                out << "}\n";
            }
        */


            PRINT_END_COMMENT(out);
        }

        void visitClear(const RamClear& clear, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << synthesiser.getRelationName(clear.getRelation()) << "->"
                << "purge();\n";
            PRINT_END_COMMENT(out);
        }

        void visitDrop(const RamDrop& drop, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);

            out << "if (!isHintsProfilingEnabled()"
                << (drop.getRelation().isTemp() ? ") " : "&& performIO) ");
            out << synthesiser.getRelationName(drop.getRelation()) << "->"
                << "purge();\n";

            PRINT_END_COMMENT(out);
        }

        void visitLogSize(const RamLogSize& size, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "ProfileEventSingleton::instance().makeQuantityEvent( R\"(";
            out << size.getMessage() << ")\",";
            out << synthesiser.getRelationName(size.getRelation()) << "->size(),iter);";
            PRINT_END_COMMENT(out);
        }

        // -- control flow statements --

        void visitSequence(const RamSequence& seq, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            for (const auto& cur : seq.getStatements()) {
                visit(cur, out);
            }
            PRINT_END_COMMENT(out);
        }

        void visitParallel(const RamParallel& parallel, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            auto stmts = parallel.getStatements();

            // special handling cases
            if (stmts.empty()) {
                PRINT_END_COMMENT(out);
                return;
            }

            // a single statement => save the overhead
            if (stmts.size() == 1) {
                visit(stmts[0], out);
                PRINT_END_COMMENT(out);
                return;
            }

            // more than one => parallel sections

            // start parallel section
            out << "SECTIONS_START;\n";

            // put each thread in another section
            for (const auto& cur : stmts) {
                out << "SECTION_START;\n";
                visit(cur, out);
                out << "SECTION_END\n";
            }

            // done
            out << "SECTIONS_END;\n";
            PRINT_END_COMMENT(out);
        }

        void visitLoop(const RamLoop& loop, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "iter = 1;\n";
            out << "for(;;) {\n";
            visit(loop.getBody(), out);
            out << "iter++;\n";
            out << "}\n";
            out << "iter = 0;\n";
            PRINT_END_COMMENT(out);
        }

        void visitSwap(const RamSwap& swap, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            const std::string& deltaKnowledge = synthesiser.getRelationName(swap.getFirstRelation());
            const std::string& newKnowledge = synthesiser.getRelationName(swap.getSecondRelation());

            out << "std::swap(" << deltaKnowledge << ", " << newKnowledge << ");\n";
            PRINT_END_COMMENT(out);
        }

        void visitExit(const RamExit& exit, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            if (exit.isInLoop()) {
                out << "if(";
                visit(exit.getCondition(), out);
                out << ") break;\n";
            } else {
                visit(exit.getCondition(), out);
                out << ";\n";
            }
            PRINT_END_COMMENT(out);
        }

        void visitLogRelationTimer(const RamLogRelationTimer& timer, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            // create local scope for name resolution
            out << "{\n";

            const std::string ext = fileExtension(Global::config().get("profile"));

            const auto& rel = timer.getRelation();
            auto relName = synthesiser.getRelationName(rel);

            out << "\tLogger logger(R\"_(" << timer.getMessage() << ")_\",iter, [&](){return " << relName
                << "->size();});\n";
            // insert statement to be measured
            visit(timer.getStatement(), out);

            // done
            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitLogTimer(const RamLogTimer& timer, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            // create local scope for name resolution
            out << "{\n";

            const std::string ext = fileExtension(Global::config().get("profile"));

            // create local timer
            out << "\tLogger logger(R\"_(" << timer.getMessage() << ")_\",iter);\n";
            // insert statement to be measured
            visit(timer.getStatement(), out);

            // done
            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitDebugInfo(const RamDebugInfo& dbg, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "SignalHandler::instance()->setMsg(R\"_(";
            out << dbg.getMessage();
            out << ")_\");\n";

            // insert statements of the rule
            visit(dbg.getStatement(), out);
            PRINT_END_COMMENT(out);
        }

        void visitStratum(const RamStratum& stratum, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "/* BEGIN STRATUM " << stratum.getIndex() << " */\n";
            if (Global::config().has("engine")) {
                // go to the stratum with the max value for int as a suffix if calling the master stratum
                auto i = stratum.getIndex();
                out << "STRATUM_" << i << ":\n";
            }
            out << "[&]() {\n";
            visit(stratum.getBody(), out);
            out << "}();\n";
            if (Global::config().has("engine")) {
                out << "if (stratumIndex != (size_t) -1) goto EXIT;\n";
            }
            out << "/* END STRATUM " << stratum.getIndex() << " */\n";
            PRINT_END_COMMENT(out);
        }

        // -- operations --

        void visitNestedOperation(const RamNestedOperation& nested, std::ostream& out) override {
            visit(nested.getOperation(), out);
            if (Global::config().has("profile") && !nested.getProfileText().empty()) {
                out << "freqs[" << synthesiser.lookupFreqIdx(nested.getProfileText()) << "]++;\n";
            }
        }

        void visitTupleOperation(const RamTupleOperation& search, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            visitNestedOperation(search, out);
            PRINT_END_COMMENT(out);
        }

        void visitParallelScan(const RamParallelScan& pscan, std::ostream& out) override {
            const auto& rel = pscan.getRelation();
            const auto& relName = synthesiser.getRelationName(rel);

            assert(pscan.getTupleId() == 0 && "not outer-most loop");

            assert(rel.getArity() > 0 && "AstTranslator failed/no parallel scans for nullaries");

            assert(!preambleIssued && "only first loop can be made parallel");
            preambleIssued = true;

            PRINT_BEGIN_COMMENT(out);

            out << "auto part = " << relName << "->partition();\n";
            out << "PARALLEL_START;\n";
            out << preamble.str();
            out << "pfor(auto it = part.begin(); it<part.end();++it){\n";
            out << "try{\n";
            out << "for(const auto& env0 : *it) {\n";

            visitTupleOperation(pscan, out);

            out << "}\n";
            out << "} catch(std::exception &e) { SignalHandler::instance()->error(e.what());}\n";
            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitScan(const RamScan& scan, std::ostream& out) override {
            const auto& rel = scan.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto id = scan.getTupleId();

            PRINT_BEGIN_COMMENT(out);

            assert(rel.getArity() > 0 && "AstTranslator failed/no scans for nullaries");

            out << "for(const auto& env" << id << " : "
                << "*" << relName << ") {\n";

            visitTupleOperation(scan, out);

            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitChoice(const RamChoice& choice, std::ostream& out) override {
            const auto& rel = choice.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto identifier = choice.getTupleId();

            assert(rel.getArity() > 0 && "AstTranslator failed/no choice for nullaries");

            PRINT_BEGIN_COMMENT(out);

            out << "for(const auto& env" << identifier << " : "
                << "*" << relName << ") {\n";
            out << "if( ";

            visit(choice.getCondition(), out);

            out << ") {\n";

            visitTupleOperation(choice, out);

            out << "break;\n";
            out << "}\n";
            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitParallelChoice(const RamParallelChoice& pchoice, std::ostream& out) override {
            const auto& rel = pchoice.getRelation();
            auto relName = synthesiser.getRelationName(rel);

            assert(pchoice.getTupleId() == 0 && "not outer-most loop");

            assert(rel.getArity() > 0 && "AstTranslator failed/no parallel choice for nullaries");

            assert(!preambleIssued && "only first loop can be made parallel");
            preambleIssued = true;

            PRINT_BEGIN_COMMENT(out);

            out << "auto part = " << relName << "->partition();\n";
            out << "PARALLEL_START;\n";
            out << preamble.str();
            out << "pfor(auto it = part.begin(); it<part.end();++it){\n";
            out << "try{\n";
            out << "for(const auto& env0 : *it) {\n";
            out << "if( ";

            visit(pchoice.getCondition(), out);

            out << ") {\n";

            visitTupleOperation(pchoice, out);

            out << "break;\n";
            out << "}\n";
            out << "}\n";
            out << "} catch(std::exception &e) { SignalHandler::instance()->error(e.what());}\n";
            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitIndexScan(const RamIndexScan& iscan, std::ostream& out) override {
            const auto& rel = iscan.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto identifier = iscan.getTupleId();
            auto keys = isa->getSearchSignature(&iscan);
            auto arity = rel.getArity();
            const auto& rangePattern = iscan.getRangePattern();

            assert(arity > 0 && "AstTranslator failed/no index scans for nullaries");

            PRINT_BEGIN_COMMENT(out);

            out << "const Tuple<RamDomain," << arity << "> key{{";
            for (size_t i = 0; i < arity; i++) {
                if (!isRamUndefValue(rangePattern[i])) {
                    visit(rangePattern[i], out);
                } else {
                    out << "0";
                }
                if (i + 1 < arity) {
                    out << ",";
                }
            }
            out << "}};\n";

            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";

            out << "auto range = " << relName << "->"
                << "equalRange_" << keys << "(key," << ctxName << ");\n";
            out << "for(const auto& env" << identifier << " : range) {\n";

            visitTupleOperation(iscan, out);

            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitParallelIndexScan(const RamParallelIndexScan& piscan, std::ostream& out) override {
            const auto& rel = piscan.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto arity = rel.getArity();
            auto keys = isa->getSearchSignature(&piscan);
            const auto& rangePattern = piscan.getRangePattern();

            assert(piscan.getTupleId() == 0 && "not outer-most loop");

            assert(arity > 0 && "AstTranslator failed/no parallel index scan for nullaries");

            assert(!preambleIssued && "only first loop can be made parallel");
            preambleIssued = true;

            PRINT_BEGIN_COMMENT(out);

            out << "const Tuple<RamDomain," << arity << "> key{{";
            for (size_t i = 0; i < arity; i++) {
                if (!isRamUndefValue(rangePattern[i])) {
                    visit(rangePattern[i], out);
                } else {
                    out << "0";
                }
                if (i + 1 < arity) {
                    out << ",";
                }
            }
            out << "}};\n";
            out << "auto range = " << relName
                << "->"
                // TODO (b-scholz): context may be missing here?
                << "equalRange_" << keys << "(key);\n";
            out << "auto part = range.partition();\n";
            out << "PARALLEL_START;\n";
            out << preamble.str();
            out << "pfor(auto it = part.begin(); it<part.end(); ++it) { \n";
            out << "try{\n";
            out << "for(const auto& env0 : *it) {\n";

            visitTupleOperation(piscan, out);

            out << "}\n";
            out << "} catch(std::exception &e) { SignalHandler::instance()->error(e.what());}\n";
            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitIndexChoice(const RamIndexChoice& ichoice, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            const auto& rel = ichoice.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto identifier = ichoice.getTupleId();
            auto arity = rel.getArity();
            const auto& rangePattern = ichoice.getRangePattern();
            auto keys = isa->getSearchSignature(&ichoice);

            // check list of keys
            assert(arity > 0 && "AstTranslator failed");

            out << "const Tuple<RamDomain," << arity << "> key{{";
            for (size_t i = 0; i < arity; i++) {
                if (!isRamUndefValue(rangePattern[i])) {
                    visit(rangePattern[i], out);
                } else {
                    out << "0";
                }
                if (i + 1 < arity) {
                    out << ",";
                }
            }
            out << "}};\n";

            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";

            out << "auto range = " << relName << "->"
                << "equalRange_" << keys << "(key," << ctxName << ");\n";
            out << "for(const auto& env" << identifier << " : range) {\n";
            out << "if( ";

            visit(ichoice.getCondition(), out);

            out << ") {\n";

            visitTupleOperation(ichoice, out);

            out << "break;\n";
            out << "}\n";
            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitParallelIndexChoice(const RamParallelIndexChoice& pichoice, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            const auto& rel = pichoice.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto arity = rel.getArity();
            const auto& rangePattern = pichoice.getRangePattern();
            auto keys = isa->getSearchSignature(&pichoice);

            assert(pichoice.getTupleId() == 0 && "not outer-most loop");

            assert(arity > 0 && "AstTranslator failed");

            assert(!preambleIssued && "only first loop can be made parallel");
            preambleIssued = true;

            PRINT_BEGIN_COMMENT(out);

            out << "const Tuple<RamDomain," << arity << "> key{{";
            for (size_t i = 0; i < arity; i++) {
                if (!isRamUndefValue(rangePattern[i])) {
                    visit(rangePattern[i], out);
                } else {
                    out << "0";
                }
                if (i + 1 < arity) {
                    out << ",";
                }
            }
            out << "}};\n";
            out << "auto range = " << relName
                << "->"
                // TODO (b-scholz): context may be missing here?
                << "equalRange_" << keys << "(key);\n";
            out << "auto part = range.partition();\n";
            out << "PARALLEL_START;\n";
            out << preamble.str();
            out << "pfor(auto it = part.begin(); it<part.end(); ++it) { \n";
            out << "try{";
            out << "for(const auto& env0 : *it) {\n";
            out << "if( ";

            visit(pichoice.getCondition(), out);

            out << ") {\n";

            visitTupleOperation(pichoice, out);

            out << "break;\n";
            out << "}\n";
            out << "}\n";
            out << "} catch(std::exception &e) { SignalHandler::instance()->error(e.what());}\n";
            out << "}\n";

            PRINT_END_COMMENT(out);
        }

        void visitUnpackRecord(const RamUnpackRecord& lookup, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            auto arity = lookup.getArity();

            // get the tuple type working with
            std::string tuple_type = "ram::Tuple<RamDomain," + toString(arity) + ">";

            // look up reference
            out << "auto ref = ";
            visit(lookup.getExpression(), out);
            out << ";\n";

            out << "if (isNull<" << tuple_type << ">(ref)) continue;\n";
            out << tuple_type << " env" << lookup.getTupleId() << " = unpack<" << tuple_type << ">(ref);\n";

            out << "{\n";

            // continue with condition checks and nested body
            visitTupleOperation(lookup, out);

            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitIndexAggregate(const RamIndexAggregate& aggregate, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            // get some properties
            const auto& rel = aggregate.getRelation();
            auto arity = rel.getArity();
            auto relName = synthesiser.getRelationName(rel);
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";
            auto identifier = aggregate.getTupleId();

            // aggregate tuple storing the result of aggregate
            std::string tuple_type = "ram::Tuple<RamDomain," + toString(arity) + ">";

            // declare environment variable
            out << "ram::Tuple<RamDomain,1> env" << identifier << ";\n";

            // get range to aggregate
            auto keys = isa->getSearchSignature(&aggregate);

            // special case: counting number elements over an unrestricted predicate
            if (aggregate.getFunction() == souffle::COUNT && keys == 0 &&
                    isRamTrue(&aggregate.getCondition())) {
                // shortcut: use relation size
                out << "env" << identifier << "[0] = " << relName << "->"
                    << "size();\n";
                visitTupleOperation(aggregate, out);
                PRINT_END_COMMENT(out);
                return;
            }

            // init result
            std::string init;
            switch (aggregate.getFunction()) {
                case souffle::MIN:
                    init = "MAX_RAM_DOMAIN";
                    break;
                case souffle::MAX:
                    init = "MIN_RAM_DOMAIN";
                    break;
                case souffle::COUNT:
                    init = "0";
                    break;
                case souffle::SUM:
                    init = "0";
                    break;
                default:
                    abort();
            }
            out << "RamDomain res" << identifier << " = " << init << ";\n";

            // check whether there is an index to use
            if (keys == 0) {
                out << "for(const auto& env" << identifier << " : "
                    << "*" << relName << ") {\n";
            } else {
                // a lambda for printing boundary key values
                auto printKeyTuple = [&]() {
                    for (size_t i = 0; i < arity; i++) {
                        if (!isRamUndefValue(aggregate.getRangePattern()[i])) {
                            visit(aggregate.getRangePattern()[i], out);
                        } else {
                            out << "0";
                        }
                        if (i + 1 < arity) {
                            out << ",";
                        }
                    }
                };

                // get index
                auto index = synthesiser.toIndex(keys);
                out << "const " << tuple_type << " key{{";
                printKeyTuple();
                out << "}};\n";
                out << "auto range = " << relName << "->"
                    << "equalRange_" << keys << "(key," << ctxName << ");\n";

                // aggregate result
                out << "for(const auto& env" << identifier << " : range) {\n";
            }

            // produce condition inside the loop
            out << "if( ";
            visit(aggregate.getCondition(), out);
            out << ") {\n";

            switch (aggregate.getFunction()) {
                case souffle::MIN:
                    out << "res" << identifier << " = std::min (res" << identifier << ",";
                    visit(aggregate.getExpression(), out);
                    out << ");\n";
                    break;
                case souffle::MAX:
                    out << "res" << identifier << " = std::max (res" << identifier << ",";
                    visit(aggregate.getExpression(), out);
                    out << ");\n";
                    break;
                case souffle::COUNT:
                    // count is easy
                    out << "++res" << identifier << "\n;";
                    break;
                case souffle::SUM:
                    out << "res" << identifier << " += ";
                    visit(aggregate.getExpression(), out);
                    out << ";\n";
                    break;
                default:
                    abort();
            }

            out << "}\n";

            // end aggregator loop
            out << "}\n";

            // write result into environment tuple
            out << "env" << identifier << "[0] = res" << identifier << ";\n";

            if (aggregate.getFunction() == souffle::MIN || aggregate.getFunction() == souffle::MAX) {
                // check whether there exists a min/max first before next loop
                // out << "if(res" << identifier << " != " << init << "){\n";
                visitTupleOperation(aggregate, out);
                // out << "}\n";
            } else {
                visitTupleOperation(aggregate, out);
            }

            PRINT_END_COMMENT(out);
        }

        void visitAggregate(const RamAggregate& aggregate, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            // get some properties
            const auto& rel = aggregate.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";
            auto identifier = aggregate.getTupleId();

            // declare environment variable
            out << "ram::Tuple<RamDomain,1> env" << identifier << ";\n";

            // special case: counting number elements over an unrestricted predicate
            if (aggregate.getFunction() == souffle::COUNT && isRamTrue(&aggregate.getCondition())) {
                // shortcut: use relation size
                out << "env" << identifier << "[0] = " << relName << "->"
                    << "size();\n";
                visitTupleOperation(aggregate, out);
                PRINT_END_COMMENT(out);
                return;
            }

            // init result
            std::string init;
            switch (aggregate.getFunction()) {
                case souffle::MIN:
                    init = "MAX_RAM_DOMAIN";
                    break;
                case souffle::MAX:
                    init = "MIN_RAM_DOMAIN";
                    break;
                case souffle::COUNT:
                    init = "0";
                    break;
                case souffle::SUM:
                    init = "0";
                    break;
                default:
                    abort();
            }
            out << "RamDomain res" << identifier << " = " << init << ";\n";

            // check whether there is an index to use
            out << "for(const auto& env" << identifier << " : "
                << "*" << relName << ") {\n";

            // produce condition inside the loop
            out << "if( ";
            visit(aggregate.getCondition(), out);
            out << ") {\n";

            // pick function
            switch (aggregate.getFunction()) {
                case souffle::MIN:
                    out << "res" << identifier << " = std::min(res" << identifier << ",";
                    visit(aggregate.getExpression(), out);
                    out << ");\n";
                    break;
                case souffle::MAX:
                    out << "res" << identifier << " = std::max(res" << identifier << ",";
                    visit(aggregate.getExpression(), out);
                    out << ");\n";
                    break;
                case souffle::COUNT:
                    out << "++res" << identifier << "\n;";
                    break;
                case souffle::SUM:
                    out << "res" << identifier << " += ";
                    visit(aggregate.getExpression(), out);
                    out << ";\n";
                    break;
                default:
                    abort();
            }

            out << "}\n";

            // end aggregator loop
            out << "}\n";

            // write result into environment tuple
            out << "env" << identifier << "[0] = res" << identifier << ";\n";

            if (aggregate.getFunction() == souffle::MIN || aggregate.getFunction() == souffle::MAX) {
                // check whether there exists a min/max first before next loop
                // out << "if(res" << identifier << " != " << init << "){\n";
                visitTupleOperation(aggregate, out);
                // out << "}\n";
            } else {
                visitTupleOperation(aggregate, out);
            }

            PRINT_END_COMMENT(out);
        }

        void visitFilter(const RamFilter& filter, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "if( ";
            visit(filter.getCondition(), out);
            out << ") {\n";
            visitNestedOperation(filter, out);
            out << "}\n";
            PRINT_END_COMMENT(out);
        }

        void visitBreak(const RamBreak& breakOp, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "if( ";
            visit(breakOp.getCondition(), out);
            out << ") break;\n";
            visitNestedOperation(breakOp, out);
            PRINT_END_COMMENT(out);
        }

        void visitProject(const RamProject& project, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            const auto& rel = project.getRelation();
            auto arity = rel.getArity();
            auto relName = synthesiser.getRelationName(rel);
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";

            // create projected tuple
            if (project.getValues().empty()) {
                out << "Tuple<RamDomain," << arity << "> tuple{{}};\n";
            } else {
                out << "Tuple<RamDomain," << arity << "> tuple{{static_cast<RamDomain>("
                    << join(project.getValues(), "),static_cast<RamDomain>(", rec) << ")}};\n";
            }

            // insert tuple
            out << relName << "->"
                << "insert(tuple," << ctxName << ");\n";

            PRINT_END_COMMENT(out);
        }

        // -- conditions --

        void visitTrue(const RamTrue& ltrue, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "true";
            PRINT_END_COMMENT(out);
        }

        void visitFalse(const RamFalse& lfalse, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "false";
            PRINT_END_COMMENT(out);
        }

        void visitConjunction(const RamConjunction& conj, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            visit(conj.getLHS(), out);
            out << " && ";
            visit(conj.getRHS(), out);
            PRINT_END_COMMENT(out);
        }

        void visitDisjunction(const RamDisjunction& disj, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "((";
            visit(disj.getLHS(), out);
            out << ") || (";
            visit(disj.getRHS(), out);
            out << "))";
            PRINT_END_COMMENT(out);
        }

        void visitNegation(const RamNegation& neg, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "!(";
            visit(neg.getOperand(), out);
            out << ")";
            PRINT_END_COMMENT(out);
        }

        void visitConstraint(const RamConstraint& rel, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            switch (rel.getOperator()) {
                // comparison operators
                case BinaryConstraintOp::EQ:
                    out << "((";
                    visit(rel.getLHS(), out);
                    out << ") == (";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                case BinaryConstraintOp::NE:
                    out << "((";
                    visit(rel.getLHS(), out);
                    out << ") != (";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                case BinaryConstraintOp::LT:
                    out << "((";
                    visit(rel.getLHS(), out);
                    out << ") < (";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                case BinaryConstraintOp::LE:
                    out << "((";
                    visit(rel.getLHS(), out);
                    out << ") <= (";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                case BinaryConstraintOp::GT:
                    out << "((";
                    visit(rel.getLHS(), out);
                    out << ") > (";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                case BinaryConstraintOp::GE:
                    out << "((";
                    visit(rel.getLHS(), out);
                    out << ") >= (";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;

                // strings
                case BinaryConstraintOp::MATCH: {
                    out << "regex_wrapper(symTable.resolve(";
                    visit(rel.getLHS(), out);
                    out << "),symTable.resolve(";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                }
                case BinaryConstraintOp::NOT_MATCH: {
                    out << "!regex_wrapper(symTable.resolve(";
                    visit(rel.getLHS(), out);
                    out << "),symTable.resolve(";
                    visit(rel.getRHS(), out);
                    out << "))";
                    break;
                }
                case BinaryConstraintOp::CONTAINS: {
                    out << "(symTable.resolve(";
                    visit(rel.getRHS(), out);
                    out << ").find(symTable.resolve(";
                    visit(rel.getLHS(), out);
                    out << ")) != std::string::npos)";
                    break;
                }
                case BinaryConstraintOp::NOT_CONTAINS: {
                    out << "(symTable.resolve(";
                    visit(rel.getRHS(), out);
                    out << ").find(symTable.resolve(";
                    visit(rel.getLHS(), out);
                    out << ")) == std::string::npos)";
                    break;
                }
                default:
                    assert(false && "Unsupported Operation!");
                    break;
            }
            PRINT_END_COMMENT(out);
        }

        void visitEmptinessCheck(const RamEmptinessCheck& emptiness, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << synthesiser.getRelationName(emptiness.getRelation()) << "->"
                << "empty()";
            PRINT_END_COMMENT(out);
        }

        void visitExistenceCheck(const RamExistenceCheck& exists, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            // get some details
            const auto& rel = exists.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";
            auto arity = rel.getArity();
            assert(arity > 0 && "AstTranslator failed");
            std::string before, after;
            if (Global::config().has("profile") && !exists.getRelation().isTemp()) {
                out << R"_((reads[)_" << synthesiser.lookupReadIdx(rel.getName()) << R"_(]++,)_";
                after = ")";
            }

            // if it is total we use the contains function
            if (isa->isTotalSignature(&exists)) {
                out << relName << "->"
                    << "contains(Tuple<RamDomain," << arity << ">{{" << join(exists.getValues(), ",", rec)
                    << "}}," << ctxName << ")" << after;
                PRINT_END_COMMENT(out);
                return;
            }

            // else we conduct a range query
            out << "!" << relName << "->"
                << "equalRange";
            out << "_" << isa->getSearchSignature(&exists);
            out << "(Tuple<RamDomain," << arity << ">{{";
            out << join(exists.getValues(), ",", [&](std::ostream& out, RamExpression* value) {
                if (!isRamUndefValue(value)) {
                    visit(*value, out);
                } else {
                    out << "0";
                }
            });
            out << "}}," << ctxName << ").empty()" << after;
            PRINT_END_COMMENT(out);
        }

        void visitPositiveExistenceCheck(const RamPositiveExistenceCheck& exists, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            // get some details
            const auto& rel = exists.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";
            auto arity = rel.getArity();
            assert(arity > 0 && "AstTranslator failed");
            std::string before, after;
            if (Global::config().has("profile") && !exists.getRelation().isTemp()) {
                out << R"_((reads[)_" << synthesiser.lookupReadIdx(rel.getName()) << R"_(]++,)_";
                after = ")";
            }

            RamExpression* currentCount = exists.getValues()[exists.getValues().size() - 1];
            // RamExpression* previousCount = exists.getValues()[exists.getValues().size() - 2];
            RamExpression* iteration = exists.getValues()[exists.getValues().size() - 2];

            out << "[&]() -> bool {\n";

            out << "auto existenceCheck = " << relName << "->"
                << "equalRange";
            out << "_" << isa->getSearchSignature(&exists);
            out << "(Tuple<RamDomain," << arity << ">{{";

            for (size_t i = 0; i < exists.getValues().size() - 2; i++) {
                RamExpression* val = exists.getValues()[i];
                if (!isRamUndefValue(val)) {
                    visit(*val, out);
                } else {
                    out << "0";
                }
                out << ",";
            }
            out << "0,0";
            out << "}}," << ctxName << ");\n";

            out << "for (const auto& tup : existenceCheck) {\n";

            if (!isRamUndefValue(currentCount)) {
                // count of 1 indicates that we want to check previous iterations
                out << "if (";
                visit(*currentCount, out);
                out << " == 1) {\n";

                // we want to encode (I_no \ Delta_o union Delta_n \ I_o)
                // if count is positive, then we find the tuple
                out << "if (tup[" << arity - 1 << "] > 0) {\n"; //  && tup[" << arity - 3 << "] == (iter-1)";

                // if tuple is in Delta_n, then it shouldn't be in I_o
                out << "if (";
                visit(*iteration, out);
                out << " == -1 || (";
                visit(*iteration, out);
                out << " <= (iter-1) && tup[" << arity - 2 << "] <= (iter - 1))";

                /*
                // if tuple is in I_no, then it shouldn't be in Delta_o
                out << "|| (";
                visit(*iteration, out);
                out << " < (iter-1) && tup[" << arity - 2 << "] <= (iter - 1))";
                */

                out << ") return true;\n";
                out << "}\n";
                out << "}\n";

                // count of 0 indicates that we want to check existence in earlier iterations
                out << "else if (";
                visit(*currentCount, out);
                out << " == 0) {\n";

                // if count is positive and iteration is lower than current, then we find the tuple
                out << "if (tup[" << arity - 1 << "] > 0 && (";
                visit(*iteration, out);
                out << " == -1 || iter == 0 || tup[" << arity - 2 << "] <= (iter-1))) {\n"; //  && tup[" << arity - 3 << "] == (iter-1)";
                /*
                out << "if (tup[" << arity - 1 << "] > 0 && tup[" << arity - 3 << "] == ";
                visit(*iteration, out);
                out << ") {\n"; //  && tup[" << arity - 3 << "] == (iter-1)";
                */
                out << "return true;\n";
                out << "}\n";
                out << "}\n";

                // count of -1 indicates that we want to check that the tuple is not deleted
                out << "else if (";
                visit(*currentCount, out);
                out << " == -1) {\n";

                // if count is positive and iteration is lower than current, then we find the tuple
                out << "if (tup[" << arity - 1 << "] <= 0) {\n";
                out << "return true;\n";
                out << "}\n";
                out << "}\n";
            }

            /*
            if (!isRamUndefValue(currentCount) && !isRamUndefValue(previousCount)) {
                out << "if (";
                visit(*currentCount, out);
                out << " > 0";
                out << " && ";
                visit(*previousCount, out);
                out << " == 0) {\n";

                // we want to encode (I_no \ Delta_o union Delta_n \ I_o)
                // if count is positive, then we find the tuple
                out << "if (tup[" << arity - 1 << "] > 0) {\n"; //  && tup[" << arity - 3 << "] == (iter-1)";

                // if tuple is in Delta_n, then it shouldn't be in I_o
                out << "if (";
                visit(*iteration, out);
                out << " == -1 || (";
                visit(*iteration, out);
                out << " == (iter-1) && tup[" << arity - 3 << "] <= (iter - 1))";

                // if tuple is in I_no, then it shouldn't be in Delta_o
                out << "|| (";
                visit(*iteration, out);
                out << " < (iter-1) && tup[" << arity - 3 << "] <= (iter - 1))";

                out << ") return true;\n";
                out << "}\n";
                out << "}\n";
            } else if (!isRamUndefValue(currentCount)) {
                out << "if (";
                visit(*currentCount, out);
                out << " > 0) {\n";

                // if count is positive and iteration is lower than current, then we find the tuple
                out << "if (tup[" << arity - 1 << "] > 0 && (iter == 0 || tup[" << arity - 3 << "] <= (iter-1))) {\n"; //  && tup[" << arity - 3 << "] == (iter-1)";
                out << "return true;\n";
                out << "}\n";
                out << "}\n";

                out << "else if (";
                visit(*currentCount, out);
                out << " == 0) {\n";

                // if count is positive and iteration is lower than current, then we find the tuple
                out << "if (tup[" << arity - 1 << "] > 0) {\n"; //  && tup[" << arity - 3 << "] == (iter-1)";
                out << "return true;\n";
                out << "}\n";

                out << "}\n";
            } else if (!isRamUndefValue(previousCount)) {
                out << "if (";
                visit(*previousCount, out);
                out << " == 0) {\n";
                out << "if (tup[" << arity - 2 << "] == 0 && tup[" << arity - 1 << "] > 0"; //  && tup[" << arity - 3 << "] < ";
                // visit(*iteration, out);
                out << ") return true;\n";
                out << "}\n";

                out << "else if (";
                visit(*previousCount, out);
                out << " == -1) {\n";
                out << "if (tup[" << arity - 2 << "] > 0 && tup[" << arity - 1 << "] <= 0"; //  && tup[" << arity - 3 << "] < ";
                // visit(*iteration, out);
                out << ") return true;\n";
                out << "}\n";
            }
            */
            out << "}\n";
            out << "return false;\n";

            out << "}()\n" << after;
            PRINT_END_COMMENT(out);
        }

        void visitSubsumptionExistenceCheck(
                const RamSubsumptionExistenceCheck& subsumptionExists, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            std::string before, after;
            // get some details
            const auto& rel = subsumptionExists.getRelation();
            auto relName = synthesiser.getRelationName(rel);
            auto ctxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(rel) + ")";
            if (Global::config().has("profile") && !subsumptionExists.getRelation().isTemp()) {
                out << R"_((reads[)_" << synthesiser.lookupReadIdx(rel.getName()) << R"_(]++,)_";
                after = ")";
            }
            /*
            const auto& diffRel = subsumptionExists.getDiffRelation();
            auto diffRelName = synthesiser.getRelationName(diffRel);
            auto diffCtxName = "READ_OP_CONTEXT(" + synthesiser.getOpContextName(diffRel) + ")";
            */
            auto arity = rel.getArity();
            auto numberOfHeights = rel.getNumberOfHeights();

            // get the iteration number
            RamExpression* iteration = subsumptionExists.getValues()[subsumptionExists.getValues().size() - 2];

            // get the value signifying whether the tuple is addition or deletion
            // RamExpression* prevCount = subsumptionExists.getValues()[subsumptionExists.getValues().size() - 2];

            // get the value signifying whether the tuple is addition or deletion
            RamExpression* count = subsumptionExists.getValues()[subsumptionExists.getValues().size() - 1];

            if (isRamUndefValue(count)) {
                return;
            }

            // provenance not exists is never total, conduct a range query
            out << "[&]() -> bool {\n";

            if (!isRamUndefValue(count)) {

                // we want to check whether the same tuple in the same iteration exists
                out << "auto existenceCheck = " << relName << "->"
                    << "equalRange";

                // the + 4 is a nasty hack that gives us the signature of the search that specifies the iteration number
                out << "_" << isa->getSearchSignature(&subsumptionExists);
                out << "(Tuple<RamDomain," << arity << ">{{";

                for (size_t i = 0; i < subsumptionExists.getValues().size() - 2; i++) {
                    RamExpression* val = subsumptionExists.getValues()[i];
                    if (!isRamUndefValue(val)) {
                        visit(*val, out);
                    } else {
                        out << "0";
                    }
                    out << ",";
                }
                out << "0,0";
                out << "}}, " << ctxName << ");\n";

                // check whether tuple is deletion
                out << "if (";
                visit(*count, out);
                out << " <= 0) {\n";

                // if deletion, then return true (i.e., don't insert) if either:
                // (1) tuple doesn't exist
                // (2) tuple exists with count of zero

                // if tuple doesn't exist, then we can't delete it
                out << "if (existenceCheck.empty()) return true;\n";

                // otherwise, only update if there is a tuple with non-zero count
                // iterate through all tuples matching the payload
                out << "for (auto& tup : existenceCheck) {\n";

                // check that the iteration matches
                out << "if (tup[" << arity - 2 << "] == ";
                visit(*iteration, out);

                // and that the count is positive
                out << " && tup[" << arity - 1 << "] > 0) ";

                // if these hold, then we can update
                out << "return false;\n";
                out << "}\n";

                // else, don't update
                out << "return true;\n";

                // if addition, we check the previous count:
                // (1) return false (i.e., update) if either existenceCheck is empty, or the only tuples found in existenceCheck have a 0 current count
                out << "} else {\n";

                // if tuple doesn't exist, then we insert it
                out << "if (existenceCheck.empty()) return false;\n";

                /*
                // otherwise, only insert if all tuples have zero count
                // iterate through all tuples matching the payload
                out << "for (auto& tup : existenceCheck) {\n";

                // this is for a special case where:
                // (1) a tuple exists in iteration i,
                // (2) is inserted in iteration j < i in a subsequent epoch
                // (3) the inserted tuple in iteration j should trigger an update in count in iteration i
                out << "if (tup[" << arity - 3 << "] == ";
                visit(*iteration, out);
                out << ") return false;\n";
                out << "}\n";
                */

                // otherwise, only insert if all tuples have zero count
                // iterate through all tuples matching the payload
                out << "for (auto& tup : existenceCheck) {\n";
                // and that the count is positive
                // out << " && tup[" << arity - 1 << "] > 0) ";
                out << "if (tup[" << arity - 2 << "] < ";
                visit(*iteration, out);
                out << " && tup[" << arity - 1 << "] > 0) ";

                // if these hold, then we don't update
                out << "return true;\n";
                out << "}\n";

                /*
                // check if this is an update of a previously generated tuple
                out << "if (";
                visit(*prevCount, out);
                out << " == ";
                visit(*count, out);
                out << ") {\n";
                */

                // the 2 indicates a re-insertion
                out << "if (";
                visit(*count, out);
                out << " == 2) {\n";

                // if it is intended to be inserting a new tuple
                // do a check if there is a tuple in the current iteration with positive count
                out << "for (auto& tup : existenceCheck) {\n";
                out << "if (tup[" << arity - 2 << "] == ";
                visit(*iteration, out);
                out << " && tup[" << arity - 1 << "] > 0) return true;\n";
                out << "}\n";
                out << "return false;\n";
                out << "}\n";
                    
                // if it's an actual update, then process it
                out << "return false;\n";

                // end of if statement
                out << "}\n";
            }


            /*
            out << "if (existenceCheck.empty()) return false; else return ((*existenceCheck.begin())["
                << arity - numberOfHeights << "] <= ";

            visit(*(subsumptionExists.getValues()[arity - numberOfHeights]), out);
            out << ")";
            */
            if (numberOfHeights > 1) {
                out << " &&  !("
                    << "(*existenceCheck.begin())[" << arity - numberOfHeights << "] == ";
                visit(*(subsumptionExists.getValues()[arity - numberOfHeights]), out);

                // out << ")";}
                out << " && (";

                out << "(*existenceCheck.begin())[" << arity - numberOfHeights + 1 << "] > ";
                visit(*(subsumptionExists.getValues()[arity - numberOfHeights + 1]), out);
                // out << "))";}
                for (int i = arity - numberOfHeights + 2; i < (int)arity; i++) {
                    out << " || (";
                    for (int j = arity - numberOfHeights + 1; j < i; j++) {
                        out << "(*existenceCheck.begin())[" << j << "] == ";
                        visit(*(subsumptionExists.getValues()[j]), out);
                        out << " && ";
                    }
                    out << "(*existenceCheck.begin())[" << i << "] > ";
                    visit(*(subsumptionExists.getValues()[i]), out);
                    out << ")";
                }

                out << "))";
            }
            out << ";}()\n" << after;
            PRINT_END_COMMENT(out);
        }

        void visitSubroutineCondition(const RamSubroutineCondition& cond, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "[&]() -> bool {\n";
            out << "std::vector<RamDomain> args;\n";
            out << "std::vector<RamDomain> ret;\n";
            out << "std::vector<bool> err;\n";
            for (auto arg : cond.getArguments()) {
                out << "args.push_back(";
                visit(*arg, out);
                out << ");\n";
            }
            out << "executeSubroutine(\"" << cond.getSubroutineName() << "\", args, ret, err);\n";
            out << "if (ret.size() == 0) return false;\n";
            out << "if (ret[0] == 0) return false; else return true;\n";
            out << "}()\n";
            PRINT_END_COMMENT(out);
        }

        // -- values --
        void visitNumber(const RamNumber& num, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "RamDomain(" << num.getConstant() << ")";
            PRINT_END_COMMENT(out);
        }

        void visitTupleElement(const RamTupleElement& access, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "env" << access.getTupleId() << "[" << access.getElement() << "]";
            PRINT_END_COMMENT(out);
        }

        void visitAutoIncrement(const RamAutoIncrement& /*inc*/, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "(ctr++)";
            PRINT_END_COMMENT(out);
        }

        void visitIterationNumber(const RamIterationNumber& /*inc*/, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "(iter)";
            PRINT_END_COMMENT(out);
        }

        void visitIntrinsicOperator(const RamIntrinsicOperator& op, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);

            switch (op.getOperator()) {
                /** Unary Functor Operators */
                case FunctorOp::ORD: {
                    visit(op.getArgument(0), out);
                    break;
                }
                case FunctorOp::STRLEN: {
                    out << "static_cast<RamDomain>(symTable.resolve(";
                    visit(op.getArgument(0), out);
                    out << ").size())";
                    break;
                }
                case FunctorOp::NEG: {
                    out << "(-(";
                    visit(op.getArgument(0), out);
                    out << "))";
                    break;
                }
                case FunctorOp::BNOT: {
                    out << "(~(";
                    visit(op.getArgument(0), out);
                    out << "))";
                    break;
                }
                case FunctorOp::LNOT: {
                    out << "(!(";
                    visit(op.getArgument(0), out);
                    out << "))";
                    break;
                }
                case FunctorOp::TOSTRING: {
                    out << "symTable.lookup(std::to_string(";
                    visit(op.getArgument(0), out);
                    out << "))";
                    break;
                }
                case FunctorOp::TONUMBER: {
                    out << "(wrapper_tonumber(symTable.resolve((size_t)";
                    visit(op.getArgument(0), out);
                    out << ")))";
                    break;
                }

                /** Binary Functor Operators */
                // arithmetic
                case FunctorOp::ADD: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") + (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::SUB: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") - (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::MUL: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") * (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::DIV: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") / (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::EXP: {
                    // Cast as int64, then back to RamDomain of int32 to avoid wrapping to negative
                    // when using int32 RamDomains
                    out << "static_cast<int64_t>(std::pow(";
                    visit(op.getArgument(0), out);
                    out << ",";
                    visit(op.getArgument(1), out);
                    out << "))";
                    break;
                }
                case FunctorOp::MOD: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") % (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::BAND: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") & (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::BOR: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") | (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::BXOR: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") ^ (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::LAND: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") && (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::LOR: {
                    out << "(";
                    visit(op.getArgument(0), out);
                    out << ") || (";
                    visit(op.getArgument(1), out);
                    out << ")";
                    break;
                }
                case FunctorOp::MAX: {
                    out << "std::max({";
                    for (auto& cur : op.getArguments()) {
                        visit(cur, out);
                        out << ", ";
                    }
                    out << "})";
                    break;
                }
                case FunctorOp::MIN: {
                    out << "std::min({";
                    for (auto& cur : op.getArguments()) {
                        visit(cur, out);
                        out << ", ";
                    }
                    out << "})";
                    break;
                }

                // strings
                case FunctorOp::CAT: {
                    out << "symTable.lookup(";
                    for (size_t i = 0; i < op.getArgCount() - 1; i++) {
                        out << "symTable.resolve(";
                        visit(op.getArgument(i), out);
                        out << ") + ";
                    }
                    out << "symTable.resolve(";
                    visit(op.getArgument(op.getArgCount() - 1), out);
                    out << "))";
                    break;
                }

                /** Ternary Functor Operators */
                case FunctorOp::SUBSTR: {
                    out << "symTable.lookup(";
                    out << "substr_wrapper(symTable.resolve(";
                    visit(op.getArgument(0), out);
                    out << "),(";
                    visit(op.getArgument(1), out);
                    out << "),(";
                    visit(op.getArgument(2), out);
                    out << ")))";
                    break;
                }

                /** Undefined */
                default: {
                    assert(false && "Unsupported Operation!");
                    break;
                }
            }
            PRINT_END_COMMENT(out);
        }

        void visitUserDefinedOperator(const RamUserDefinedOperator& op, std::ostream& out) override {
            const std::string& name = op.getName();
            const std::string& type = op.getType();
            size_t arity = type.length() - 1;

            if (type[arity] == 'S') {
                out << "symTable.lookup(";
            }
            out << name << "(";

            for (size_t i = 0; i < arity; i++) {
                if (i > 0) {
                    out << ",";
                }
                if (type[i] == 'N') {
                    out << "((RamDomain)";
                    visit(op.getArgument(i), out);
                    out << ")";
                } else {
                    out << "symTable.resolve((RamDomain)";
                    visit(op.getArgument(i), out);
                    out << ").c_str()";
                }
            }
            out << ")";
            if (type[arity] == 'S') {
                out << ")";
            }
        }

        // -- records --

        void visitPackRecord(const RamPackRecord& pack, std::ostream& out) override {
            PRINT_BEGIN_COMMENT(out);
            out << "pack("
                << "ram::Tuple<RamDomain," << pack.getArguments().size() << ">({"
                << join(pack.getArguments(), ",", rec) << "})"
                << ")";
            PRINT_END_COMMENT(out);
        }

        // -- subroutine argument --

        void visitSubroutineArgument(const RamSubroutineArgument& arg, std::ostream& out) override {
            out << "(args)[" << arg.getArgument() << "]";
        }

        // -- subroutine return --

        void visitSubroutineReturnValue(const RamSubroutineReturnValue& ret, std::ostream& out) override {
            out << "std::lock_guard<std::mutex> guard(lock);\n";
            for (auto val : ret.getValues()) {
                if (isRamUndefValue(val)) {
                    out << "ret.push_back(0);\n";
                    out << "err.push_back(true);\n";
                } else {
                    out << "ret.push_back(";
                    visit(val, out);
                    out << ");\n";
                    out << "err.push_back(false);\n";
                }
            }
        }

        // -- safety net --

        void visitUndefValue(const RamUndefValue& undef, std::ostream& /*out*/) override {
            assert(false && "Compilation error");
        }

        void visitNode(const RamNode& node, std::ostream& /*out*/) override {
            std::cerr << "Unsupported node type: " << typeid(node).name() << "\n";
            assert(false && "Unsupported Node Type!");
        }
    };

    // emit code
    CodeEmitter(*this).visit(stmt, out);
}

void Synthesiser::generateCode(std::ostream& os, const std::string& id, bool& withSharedLibrary) {
    // ---------------------------------------------------------------
    //                      Auto-Index Generation
    // ---------------------------------------------------------------
    const SymbolTable& symTable = translationUnit.getSymbolTable();
    const RamProgram& prog = *translationUnit.getProgram();
    auto* idxAnalysis = translationUnit.getAnalysis<RamIndexAnalysis>();

    // ---------------------------------------------------------------
    //                      Code Generation
    // ---------------------------------------------------------------

    withSharedLibrary = false;

    std::string classname = "Sf_" + id;

    // generate C++ program
    os << "\n#include \"souffle/CompiledSouffle.h\"\n";
    if (Global::config().has("provenance")) {
        os << "#include <mutex>\n";
        os << "#include \"souffle/Explain.h\"\n";
    }

    if (Global::config().has("incremental")) {
        os << "#include <mutex>\n";
        os << "#include \"souffle/Incremental.h\"\n";
    }

    if (Global::config().has("live-profile")) {
        os << "#include <thread>\n";
        os << "#include \"souffle/profile/Tui.h\"\n";
    }
    os << "\n";
    // produce external definitions for user-defined functors
    std::map<std::string, std::string> functors;
    visitDepthFirst(prog, [&](const RamUserDefinedOperator& op) {
        if (functors.find(op.getName()) == functors.end())
            functors.insert(std::make_pair(op.getName(), op.getType()));
        withSharedLibrary = true;
    });
    os << "extern \"C\" {\n";
    for (const auto& f : functors) {
        size_t arity = f.second.length() - 1;
        const std::string& type = f.second;
        const std::string& name = f.first;
        if (type[arity] == 'N') {
            os << "souffle::RamDomain ";
        } else if (type[arity] == 'S') {
            os << "const char * ";
        }
        os << name << "(";
        std::vector<std::string> args;
        for (size_t i = 0; i < arity; i++) {
            if (type[i] == 'N') {
                args.push_back("souffle::RamDomain");
            } else {
                args.push_back("const char *");
            }
        }
        os << join(args, ",");
        os << ");\n";
    }
    os << "}\n";
    os << "\n";
    os << "namespace souffle {\n";
    os << "using namespace ram;\n";

    visitDepthFirst((prog), [&](const RamCreate& create) {
        // get some table details
        const RamRelation& rel = create.getRelation();
        const std::string& raw_name = rel.getName();

        bool isProvInfo = raw_name.find("@info") != std::string::npos || raw_name.find("@max_iter") != std::string::npos || raw_name.find("@indexed") != std::string::npos || raw_name.find("@restricted") != std::string::npos;
        auto relationType = SynthesiserRelation::getSynthesiserRelation(
                rel, idxAnalysis->getIndexes(rel), (Global::config().has("provenance") || Global::config().has("incremental")) && !isProvInfo);

        generateRelationTypeStruct(os, std::move(relationType));
    });
    os << '\n';

    os << "class " << classname << " : public SouffleProgram {\n";

    // regex wrapper
    os << "private:\n";
    os << "static inline bool regex_wrapper(const std::string& pattern, const std::string& text) {\n";
    os << "   bool result = false; \n";
    os << "   try { result = std::regex_match(text, std::regex(pattern)); } catch(...) { \n";
    os << "     std::cerr << \"warning: wrong pattern provided for match(\\\"\" << pattern << \"\\\",\\\"\" "
          "<< text << \"\\\").\\n\";\n}\n";
    os << "   return result;\n";
    os << "}\n";

    // substring wrapper
    os << "private:\n";
    os << "static inline std::string substr_wrapper(const std::string& str, size_t idx, size_t len) {\n";
    os << "   std::string result; \n";
    os << "   try { result = str.substr(idx,len); } catch(...) { \n";
    os << "     std::cerr << \"warning: wrong index position provided by substr(\\\"\";\n";
    os << "     std::cerr << str << \"\\\",\" << (int32_t)idx << \",\" << (int32_t)len << \") "
          "functor.\\n\";\n";
    os << "   } return result;\n";
    os << "}\n";

    // to number wrapper
    os << "private:\n";
    os << "static inline RamDomain wrapper_tonumber(const std::string& str) {\n";
    os << "   RamDomain result=0; \n";
    os << "   try { result = stord(str); } catch(...) { \n";
    os << "     std::cerr << \"error: wrong string provided by to_number(\\\"\";\n";
    os << R"(     std::cerr << str << "\") )";
    os << "functor.\\n\";\n";
    os << "     raise(SIGFPE);\n";
    os << "   } return result;\n";
    os << "}\n";

    if (Global::config().has("profile")) {
        os << "std::string profiling_fname;\n";
    }

    os << "public:\n";

    // declare symbol table
    os << "// -- initialize symbol table --\n";

    os << "SymbolTable symTable\n";
    if (symTable.size() > 0) {
        os << "{\n";
        for (size_t i = 0; i < symTable.size(); i++) {
            os << "\tR\"_(" << symTable.resolve(i) << ")_\",\n";
        }
        os << "}";
    }
    os << ";";

    size_t numFreq = 0;
    size_t numRead = 0;
    if (Global::config().has("profile")) {
        os << "private:\n";
        visitDepthFirst(prog, [&](const RamStatement& node) { numFreq++; });
        os << "  size_t freqs[" << numFreq << "]{};\n";
        visitDepthFirst(prog, [&](const RamCreate& node) {
            if (!node.getRelation().isTemp()) numRead++;
        });
        os << "  size_t reads[" << numRead << "]{};\n";
    }

    // print relation definitions
    std::string initCons;     // initialization of constructor
    std::string registerRel;  // registration of relations
    int relCtr = 0;
    std::string tempType;  // string to hold the type of the temporary relations
    std::string diffAppliedType;
    std::string diffMinusAppliedType;
    std::set<std::string> storeRelations;
    std::set<std::string> loadRelations;
    visitDepthFirst((prog),
            [&](const RamStore& store) { storeRelations.insert(store.getRelation().getName()); });
    visitDepthFirst((prog),
            [&](const RamLoad& load) { loadRelations.insert(load.getRelation().getName()); });
    visitDepthFirst((prog), [&](const RamCreate& create) {
            /*
        // get some table details
        const auto& rel = create.getRelation();
        int arity = rel.getArity();
        int numberOfHeights = rel.getNumberOfHeights();
        const std::string& raw_name = rel.getName();
        const std::string& name = getRelationName(rel);

        // TODO: make this correct
        // ensure that the type of the new knowledge is the same as that of the delta knowledge
        bool isDelta = rel.isTemp() && raw_name.find("@delta") != std::string::npos;
        bool isProvInfo = raw_name.find("@info") != std::string::npos || raw_name.find("@max_iter") != std::string::npos || raw_name.find("@indexed") != std::string::npos;
        auto relationType = SynthesiserRelation::getSynthesiserRelation(
                rel, idxAnalysis->getIndexes(rel), (Global::config().has("provenance") || Global::config().has("incremental")) && !isProvInfo);
        tempType = isDelta ? relationType->getTypeName() : tempType;

        // tempType means a cached version of the type, which is necessary for new and delta versions of the relations to have the same type
        // i.e., tempType = type of new relation, then delta = tempType so the types match
        // however, in the case of provenance or incremental, some relations e.g. @info or @indexed are counted as temp types, but should have their own type because there is no corresponding new type
        const std::string& type = (rel.isTemp()) && raw_name.find("new_diff_plus@") == std::string::npos && raw_name.find("new_diff_minus@") == std::string::npos && !isProvInfo ? tempType : relationType->getTypeName();
        */

        // get details of the relation
        const auto& rel = create.getRelation();
        int arity = rel.getArity();
        int numberOfHeights = rel.getNumberOfHeights();
        const std::string& raw_name = rel.getName();
        const std::string& name = getRelationName(rel);

        std::string type;

        if (Global::config().has("incremental")) {
            bool isDiffMinusApplied = raw_name.find("diff_minus_applied@") != std::string::npos;
            bool isDiffApplied = raw_name.find("diff_applied@") != std::string::npos;

            // we consider diff_applied to be normal also
            bool isNormalRelation = raw_name.find("diff_minus@") == std::string::npos && raw_name.find("diff_plus@") == std::string::npos && raw_name.find("applied@") == std::string::npos; // && raw_name.find("@delta") != std::string::npos;
            bool isSpecial = raw_name.find("@max_iter") != std::string::npos || raw_name.find("@indexed") != std::string::npos || raw_name.find("@restricted") != std::string::npos || raw_name.find("@info") != std::string::npos;

            auto relationType = SynthesiserRelation::getSynthesiserRelation(
                    rel, idxAnalysis->getIndexes(rel), true && !isSpecial);
            type = relationType->getTypeName();

            // set diffAppliedType
            if (isDiffApplied) {
                diffAppliedType = relationType->getTypeName();
            }

            /*
            // set diffMinusAppliedType
            if (isDiffMinusApplied) {
                // diffMinusAppliedType = relationType->getTypeName();

                type = diffAppliedType;
            }
            */

            // if it's a normal relation, we want to use the same type as diff_applied
            if (isNormalRelation && !isSpecial) {
                    type = diffAppliedType;
                // }

            }
        } else {
            bool isDelta = rel.isTemp() && raw_name.find("@delta") != std::string::npos;
            bool isProvInfo = raw_name.find("@info") != std::string::npos;

            auto relationType = SynthesiserRelation::getSynthesiserRelation(
                    rel, idxAnalysis->getIndexes(rel), Global::config().has("provenance") && !isProvInfo);
            type = relationType->getTypeName();

            // store the temp type for delta relations
            if (isDelta) {
                tempType = type;
            }

            // if the relation is new, use the same type as the delta
            if (rel.isTemp() && !isDelta) {
                type = tempType;
            }
        }

        // defining table
        os << "// -- Table: " << raw_name << "\n";

        os << "std::unique_ptr<" << type << "> " << name << " = std::make_unique<" << type << ">();\n";
        if (!rel.isTemp()) {
            os << "souffle::RelationWrapper<";
            os << relCtr++ << ",";
            os << type << ",";
            os << "Tuple<RamDomain," << arity << ">,";
            os << arity << ",";
            os << numberOfHeights;
            os << "> wrapper_" << name << ";\n";

            // construct types
            std::string tupleType = "std::array<const char *," + std::to_string(arity) + ">{{";
            std::string tupleName = "std::array<const char *," + std::to_string(arity) + ">{{";

            if (rel.getArity()) {
                tupleType += "\"" + rel.getArgTypeQualifier(0) + "\"";
                for (int i = 1; i < arity; i++) {
                    tupleType += ",\"" + rel.getArgTypeQualifier(i) + "\"";
                }

                tupleName += "\"" + rel.getArg(0) + "\"";
                for (int i = 1; i < arity; i++) {
                    tupleName += ",\"" + rel.getArg(i) + "\"";
                }
            }
            tupleType += "}}";
            tupleName += "}}";

            if (!initCons.empty()) {
                initCons += ",\n";
            }
            initCons += "\nwrapper_" + name + "(" + "*" + name + ",symTable,\"" + raw_name + "\"," +
                        tupleType + "," + tupleName + ")";
            registerRel += "addRelation(\"" + raw_name + "\",&wrapper_" + name + ",";
            registerRel += (loadRelations.count(rel.getName()) > 0) ? "true" : "false";
            registerRel += ",";
            registerRel += (storeRelations.count(rel.getName()) > 0) ? "true" : "false";
            registerRel += ");\n";
        }
    });

    os << "public:\n";

    // -- constructor --

    os << classname;
    if (Global::config().has("profile")) {
        os << "(std::string pf=\"profile.log\") : profiling_fname(pf)";
        if (!initCons.empty()) {
            os << ",\n" << initCons;
        }
    } else {
        os << "()";
        if (!initCons.empty()) {
            os << " : " << initCons;
        }
    }
    os << "{\n";
    if (Global::config().has("profile")) {
        os << "ProfileEventSingleton::instance().setOutputFile(profiling_fname);\n";
    }
    os << registerRel;
    os << "}\n";
    // -- destructor --

    os << "~" << classname << "() {\n";
    os << "}\n";

    // epoch number
    if (Global::config().has("incremental")) {
        os << "int epochNumber = 0;\n";
    }

    os << "private:\n";
    // issue state variables for the evaluation
    os << "std::string inputDirectory;\n";
    os << "std::string outputDirectory;\n";
    os << "bool performIO;\n";
    os << "std::atomic<RamDomain> ctr{};\n\n";
    os << "std::atomic<size_t> iter{};\n";

    // store a duration measuring I/O time - we subtract this from full runtime
    os << "std::chrono::microseconds ioTime;\n";

    // -- run function --
    os << "private:\nvoid runFunction(std::string inputDirectory = \".\", "
          "std::string outputDirectory = \".\", size_t stratumIndex = (size_t) -1, bool performIO = false) "
          "{\n";

    os << "this->inputDirectory = inputDirectory;\n";
    os << "this->outputDirectory = outputDirectory;\n";
    os << "this->performIO = performIO;\n";

    // reset I/O timer
    os << "ioTime = std::chrono::microseconds::zero();\n";

    // start evaluation timer
    os << "auto evalStart = std::chrono::high_resolution_clock::now();\n";

    os << "SignalHandler::instance()->set();\n";
    if (Global::config().has("verbose")) {
        os << "SignalHandler::instance()->enableLogging();\n";
    }

    if (Global::config().has("incremental") && Global::config().has("profile")) {
        os << "ProfileEventSingleton::instance().setOutputFile(profiling_fname + std::to_string(epochNumber++));\n";

        os << "for (size_t i = 0; i < " << numFreq << "; i++) { freqs[i] = 0; }\n";
        os << "for (size_t i = 0; i < " << numRead << "; i++) { reads[i] = 0; }\n";

        os << "ProfileEventSingleton::instance().clear();\n";
    }


    // set default threads (in embedded mode)
    // if this is not set, and omp is used, the default omp setting of number of cores is used.
    os << "#if defined(_OPENMP)\n";
    os << "if (getNumThreads() > 0) {omp_set_num_threads(getNumThreads());}\n";
    os << "#endif\n\n";

    // add actual program body
    os << "// -- query evaluation --\n";
    if (Global::config().has("profile")) {
        os << "ProfileEventSingleton::instance().startTimer();\n";
        os << R"_(ProfileEventSingleton::instance().makeTimeEvent("@time;starttime");)_" << '\n';
        os << "{\n"
           << R"_(Logger logger("@runtime;", 0);)_" << '\n';
        // Store count of relations
        size_t relationCount = 0;
        visitDepthFirst((prog), [&](const RamCreate& create) {
            if (create.getRelation().getName()[0] != '@') ++relationCount;
        });
        // Store configuration
        os << R"_(ProfileEventSingleton::instance().makeConfigRecord("relationCount", std::to_string()_"
           << relationCount << "));";
        // Outline stratum records for faster compilation
        os << "[](){\n";

        // Record relations created in each stratum
        visitDepthFirst((prog), [&](const RamStratum& stratum) {
            std::map<std::string, size_t> relNames;
            visitDepthFirst(stratum, [&](const RamCreate& create) {
                relNames[create.getRelation().getName()] = create.getRelation().getArity();
            });
            for (const auto& cur : relNames) {
                // Skip temporary relations, marked with '@'
                if (cur.first[0] == '@') {
                    continue;
                }
                os << "ProfileEventSingleton::instance().makeStratumRecord(" << stratum.getIndex()
                   << R"_(, "relation", ")_" << cur.first << R"_(", "arity", ")_" << cur.second << R"_(");)_"
                   << '\n';
            }
        });
        // End stratum record outlining
        os << "}();\n";
    }

    if (Global::config().has("engine")) {
        std::stringstream ss;
        bool hasAtLeastOneStrata = false;
        visitDepthFirst(*(prog.getMain()), [&](const RamStratum& stratum) {
            hasAtLeastOneStrata = true;
            // go to stratum of index in switch
            auto i = stratum.getIndex();
            ss << "case " << i << ":\ngoto STRATUM_" << i << ";\nbreak;\n";
        });
        if (hasAtLeastOneStrata) {
            os << "switch (stratumIndex) {\n";
            {
                // otherwise use stratum 0 if index is -1
                os << "case (size_t) -1:\ngoto STRATUM_0;\nbreak;\n";
            }
            os << ss.str();
            os << "}\n";
        }
    }

    // Set up stratum
    visitDepthFirst(*(prog.getMain()), [&](const RamStratum& stratum) {
            /*
        os << "/ * BEGIN STRATUM " << stratum.getIndex() << " * /\n";
        if (Global::config().has("engine")) {
            // go to the stratum with the max value for int as a suffix if calling the master stratum
            auto i = stratum.getIndex();
            os << "STRATUM_" << i << ":\n";
        }
        os << "[&]() {\n";
        emitCode(os, stratum.getBody());
        os << "}();\n";
        if (Global::config().has("engine")) {
            os << "if (stratumIndex != (size_t) -1) goto EXIT;\n";
        }
        os << "/ * END STRATUM " << stratum.getIndex() << " * /\n";
        */

        emitCode(os, stratum);
    });

    if (Global::config().has("engine")) {
        os << "EXIT:{}";
    }

    /*
    if (Global::config().has("incremental")) {
        os << "std::vector<RamDomain> args;\n";
        os << "std::vector<RamDomain> ret;\n";
        os << "std::vector<bool> err;\n";
        os << "executeSubroutine(\"incremental_cleanup\", args, ret, err);\n";
    }
    */

    if (Global::config().has("profile")) {
        os << "}\n";
        os << "ProfileEventSingleton::instance().stopTimer();\n";
        os << "dumpFreqs();\n";
    }

    // add code printing hint statistics
    os << "\n// -- relation hint statistics --\n";
    os << "if(isHintsProfilingEnabled()) {\n";
    os << "std::cout << \" -- Operation Hint Statistics --\\n\";\n";
    visitDepthFirst((prog), [&](const RamCreate& create) {
        auto name = getRelationName(create.getRelation());
        /*
        os << "std::cout << \"Relation " << name << ":\\n\";\n";
        os << name << "->printHintStatistics(std::cout,\"  \");\n";
        os << "std::cout << \"\\n\";\n";
        */
    });
    os << "}\n";

    os << "SignalHandler::instance()->reset();\n";

    if (Global::config().has("incremental") && Global::config().has("profile")) {
        os << "ProfileEventSingleton::instance().dump();\n";
    }

    os << "auto evalEnd = std::chrono::high_resolution_clock::now();\n";
    os << "auto evalTime = std::chrono::duration_cast<std::chrono::microseconds>(evalEnd - evalStart) - ioTime;\n";
    os << "if (isRuntimePrintingEnabled()) std::cout << \"eval-time:\" << evalTime.count() << std::endl;\n";

    // reset I/O timer
    os << "ioTime = std::chrono::microseconds::zero();\n";

    os << "}\n";  // end of runFunction() method

    // add methods to run with and without performing IO (mainly for the interface)
    os << "public:\nvoid run(size_t stratumIndex = (size_t) -1) override { runFunction(\".\", \".\", "
          "stratumIndex, false); }\n";
    os << "public:\nvoid runAll(std::string inputDirectory = \".\", std::string outputDirectory = \".\", "
          "size_t stratumIndex = (size_t) -1) "
          "override { ";
    if (Global::config().has("live-profile")) {
        os << "std::thread profiler([]() { profile::Tui().runProf(); });\n";
    }
    os << "runFunction(inputDirectory, outputDirectory, stratumIndex, true);\n";
    if (Global::config().has("live-profile")) {
        os << "if (profiler.joinable()) { profiler.join(); }\n";
    }
    os << "}\n";

    // issue printAll method
    os << "public:\n";
    os << "void printAll(std::string outputDirectory = \".\") override {\n";
    visitDepthFirst(*(prog.getMain()), [&](const RamStatement& node) {
        if (auto store = dynamic_cast<const RamStore*>(&node)) {
            std::vector<bool> symbolMask;
            for (auto& cur : store->getRelation().getAttributeTypeQualifiers()) {
                symbolMask.push_back(cur[0] == 's');
            }
            for (IODirectives ioDirectives : store->getIODirectives()) {
                os << "try {";
                os << "std::map<std::string, std::string> directiveMap(" << ioDirectives << ");\n";
                os << R"_(if (!outputDirectory.empty() && directiveMap["IO"] == "file" && )_";
                os << "directiveMap[\"filename\"].front() != '/') {";
                os << R"_(directiveMap["filename"] = outputDirectory + "/" + directiveMap["filename"];)_";
                os << "}\n";
                os << "IODirectives ioDirectives(directiveMap);\n";
                os << "IOSystem::getInstance().getWriter(";
                os << "std::vector<bool>({" << join(symbolMask) << "})";
                os << ", symTable, ioDirectives, " << (Global::config().has("incremental") ? "true" : "false");
                os << ", " << store->getRelation().getNumberOfHeights();
                os << ")->writeAll(*" << getRelationName(store->getRelation()) << ");\n";

                os << "} catch (std::exception& e) {std::cerr << e.what();exit(1);}\n";
            }
        }
    });
    os << "}\n";  // end of printAll() method

    // issue loadAll method
    os << "public:\n";
    os << "void loadAll(std::string inputDirectory = \".\") override {\n";
    visitDepthFirst(*(prog.getMain()), [&](const RamLoad& load) {
        // get some table details
        std::vector<bool> symbolMask;
        for (auto& cur : load.getRelation().getAttributeTypeQualifiers()) {
            symbolMask.push_back(cur[0] == 's');
        }
        for (IODirectives ioDirectives : load.getIODirectives()) {
            os << "try {";
            os << "std::map<std::string, std::string> directiveMap(";
            os << ioDirectives << ");\n";
            os << R"_(if (!inputDirectory.empty() && directiveMap["IO"] == "file" && )_";
            os << "directiveMap[\"filename\"].front() != '/') {";
            os << R"_(directiveMap["filename"] = inputDirectory + "/" + directiveMap["filename"];)_";
            os << "}\n";
            os << "IODirectives ioDirectives(directiveMap);\n";
            os << "IOSystem::getInstance().getReader(";
            os << "std::vector<bool>({" << join(symbolMask) << "})";
            os << ", symTable, ioDirectives";
            os << ", " << (Global::config().has("incremental") ? "true" : "false");
            os << ", " << load.getRelation().getNumberOfHeights();
            os << ")->readAll(*" << getRelationName(load.getRelation());
            os << ");\n";
            os << "} catch (std::exception& e) {std::cerr << \"Error loading data: \" << e.what() << "
                  "'\\n';}\n";
        }
    });
    os << "}\n";  // end of loadAll() method

    // issue dump methods
    auto dumpRelation = [&](const std::string& name, const std::vector<std::string>& mask, size_t arity,
                                size_t numberOfHeights) {
        auto relName = name;
        std::vector<bool> symbolMask;
        for (auto& cur : mask) {
            symbolMask.push_back(cur[0] == 's');
        }

        os << "try {";
        os << "IODirectives ioDirectives;\n";
        os << "ioDirectives.setIOType(\"stdout\");\n";
        os << "ioDirectives.setRelationName(\"" << name << "\");\n";
        os << "IOSystem::getInstance().getWriter(";
        os << "std::vector<bool>({" << join(symbolMask) << "})";
        os << ", symTable, ioDirectives, " << (Global::config().has("incremental") ? "true" : "false");
        os << ", " << numberOfHeights;
        os << ")->writeAll(*" << relName << ");\n";
        os << "} catch (std::exception& e) {std::cerr << e.what();exit(1);}\n";
    };

    // dump inputs
    os << "public:\n";
    os << "void dumpInputs(std::ostream& out = std::cout) override {\n";
    visitDepthFirst(*(prog.getMain()), [&](const RamLoad& load) {
        auto& name = getRelationName(load.getRelation());
        auto& mask = load.getRelation().getAttributeTypeQualifiers();
        size_t arity = load.getRelation().getArity();
        dumpRelation(name, mask, arity, load.getRelation().getNumberOfHeights());
    });
    os << "}\n";  // end of dumpInputs() method

    // dump outputs
    os << "public:\n";
    os << "void dumpOutputs(std::ostream& out = std::cout) override {\n";
    visitDepthFirst(*(prog.getMain()), [&](const RamStore& store) {
        auto& name = getRelationName(store.getRelation());
        auto& mask = store.getRelation().getAttributeTypeQualifiers();
        size_t arity = store.getRelation().getArity();
        dumpRelation(name, mask, arity, store.getRelation().getNumberOfHeights());
    });
    os << "}\n";  // end of dumpOutputs() method

    os << "public:\n";
    os << "SymbolTable& getSymbolTable() override {\n";
    os << "return symTable;\n";
    os << "}\n";  // end of getSymbolTable() method

    // TODO: generate code for subroutines
    if (Global::config().has("provenance") || Global::config().has("incremental")) {
        if (Global::config().get("provenance") == "subtreeHeights") {
            // method that populates provenance indices
            os << "void copyIndex() {\n";
            visitDepthFirst(*(prog.getMain()), [&](const RamCreate& create) {
                // get some table details
                const auto& rel = create.getRelation();
                const std::string& name = getRelationName(rel);
                const std::string& raw_name = rel.getName();

                bool isProvInfo = raw_name.find("@info") != std::string::npos || raw_name.find("@max_iter") != std::string::npos || raw_name.find("@indexed") != std::string::npos || raw_name.find("@restricted") != std::string::npos;
                auto relationType = SynthesiserRelation::getSynthesiserRelation(
                        rel, idxAnalysis->getIndexes(rel), Global::config().has("provenance") && !isProvInfo);

                if (!relationType->getProvenenceIndexNumbers().empty()) {
                    os << name << "->copyIndex();\n";
                }
            });
            os << "}\n";
        }

        // generate subroutine adapter
        os << "void executeSubroutine(std::string name, const std::vector<RamDomain>& args, "
              "std::vector<RamDomain>& ret, std::vector<bool>& err) override {\n";

        // subroutine number
        size_t subroutineNum = 0;
        for (auto& sub : prog.getSubroutines()) {
            os << "if (name == \"" << sub.first << "\") {\n";

            // only generate timers for update subroutine
            if (sub.first == "update") {
                if (Global::config().has("profile")) {
                    // reset reads and frequencies for profiler
                    os << "for (size_t i = 0; i < " << numFreq << "; i++) { freqs[i] = 0; }\n";
                    os << "for (size_t i = 0; i < " << numRead << "; i++) { reads[i] = 0; }\n";
                }

                // reset I/O timer
                os << "ioTime = std::chrono::microseconds::zero();\n";
                os << "auto updateStart = std::chrono::high_resolution_clock::now();\n";
            }

            os << "subproof_" << subroutineNum
               << "(args, ret, err);\n";  // subproof_i to deal with special characters in relation names

            // only generate timers for update subroutine
            if (sub.first == "update") {
                os << "auto updateEnd = std::chrono::high_resolution_clock::now();\n";
                os << "auto updateTime = std::chrono::duration_cast<std::chrono::microseconds>(updateEnd - updateStart) - ioTime;\n";
                os << "if (isRuntimePrintingEnabled()) std::cout << \"update-time:\" << updateTime.count() << std::endl;\n";

                if (Global::config().has("profile")) {
                    // reset reads and frequencies for profiler
                    os << "dumpFreqs();\n";
                }

                // reset I/O timer
                os << "ioTime = std::chrono::microseconds::zero();\n";
            }

            os << "}\n";
            subroutineNum++;
        }
        os << "}\n";  // end of executeSubroutine

        // generate method for each subroutine
        subroutineNum = 0;
        for (auto& sub : prog.getSubroutines()) {
            // method header
            os << "void "
               << "subproof_" << subroutineNum
               << "(const std::vector<RamDomain>& args, "
                  "std::vector<RamDomain>& ret, std::vector<bool>& err) {\n";

            // a lock is needed when filling the subroutine return vectors
            os << "std::mutex lock;\n";

            // generate code for body
            emitCode(os, *sub.second);

            os << "return;\n";
            os << "}\n";  // end of subroutine
            subroutineNum++;
        }
    }

    // dumpFreqs method
    if (Global::config().has("profile")) {
        os << "private:\n";
        os << "void dumpFreqs() {\n";
        for (auto const& cur : idxMap) {
            os << "\tProfileEventSingleton::instance().makeQuantityEvent(R\"_(" << cur.first << ")_\", freqs["
               << cur.second << "],0);\n";
        }
        for (auto const& cur : neIdxMap) {
            os << "\tProfileEventSingleton::instance().makeQuantityEvent(R\"_(@relation-reads;" << cur.first
               << ")_\", reads[" << cur.second << "],0);\n";
        }
        os << "}\n";  // end of dumpFreqs() method
    }

    os << "};\n";  // end of class declaration

    // hidden hooks
    os << "SouffleProgram *newInstance_" << id << "(){return new " << classname << ";}\n";
    os << "SymbolTable *getST_" << id << "(SouffleProgram *p){return &reinterpret_cast<" << classname
       << "*>(p)->symTable;}\n";

    os << "\n#ifdef __EMBEDDED_SOUFFLE__\n";
    os << "class factory_" << classname << ": public souffle::ProgramFactory {\n";
    os << "SouffleProgram *newInstance() {\n";
    os << "return new " << classname << "();\n";
    os << "};\n";
    os << "public:\n";
    os << "factory_" << classname << "() : ProgramFactory(\"" << id << "\"){}\n";
    os << "};\n";
    os << "static factory_" << classname << " __factory_" << classname << "_instance;\n";
    os << "}\n";
    os << "#else\n";
    os << "}\n";
    os << "int main(int argc, char** argv)\n{\n";
    os << "try{\n";

    // parse arguments
    os << "souffle::CmdOptions opt(";
    os << "R\"(" << Global::config().get("") << ")\",\n";
    os << "R\"(.)\",\n";
    os << "R\"(.)\",\n";
    if (Global::config().has("profile")) {
        os << "true,\n";
        os << "R\"(" << Global::config().get("profile") << ")\",\n";
    } else {
        os << "false,\n";
        os << "R\"()\",\n";
    }
    os << std::stoi(Global::config().get("jobs")) << ",\n";
    os << "-1";
    os << ");\n";

    os << "if (!opt.parse(argc,argv)) return 1;\n";

    os << "souffle::";
    if (Global::config().has("profile")) {
        os << classname + " obj(opt.getProfileName());\n";
    } else {
        os << classname + " obj;\n";
    }

    os << "#if defined(_OPENMP) \n";
    os << "obj.setNumThreads(opt.getNumJobs());\n";
    os << "\n#endif\n";

    if (Global::config().has("profile")) {
        os << R"_(souffle::ProfileEventSingleton::instance().makeConfigRecord("", opt.getSourceFileName());)_"
           << '\n';
        os << R"_(souffle::ProfileEventSingleton::instance().makeConfigRecord("fact-dir", opt.getInputFileDir());)_"
           << '\n';
        os << R"_(souffle::ProfileEventSingleton::instance().makeConfigRecord("jobs", std::to_string(opt.getNumJobs()));)_"
           << '\n';
        os << R"_(souffle::ProfileEventSingleton::instance().makeConfigRecord("output-dir", opt.getOutputFileDir());)_"
           << '\n';
        os << R"_(souffle::ProfileEventSingleton::instance().makeConfigRecord("version", ")_"
           << Global::config().get("version") << R"_(");)_" << '\n';
    }
    os << "obj.runAll(opt.getInputFileDir(), opt.getOutputFileDir(), opt.getStratumIndex());\n";

    if (Global::config().get("provenance") == "explain") {
        os << "explain(obj, false, false);\n";
    } else if (Global::config().get("provenance") == "subtreeHeights") {
        os << "obj.copyIndex();\n";
        os << "explain(obj, false, true);\n";
    } else if (Global::config().get("provenance") == "explore") {
        os << "explain(obj, true, false);\n";
    }

    if (Global::config().has("incremental")) {
        os << "startIncremental(obj, opt);\n";
    }
    os << "return 0;\n";
    os << "} catch(std::exception &e) { souffle::SignalHandler::instance()->error(e.what());}\n";
    os << "}\n";
    os << "\n#endif\n";
}

}  // end of namespace souffle
