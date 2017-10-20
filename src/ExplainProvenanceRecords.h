/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ExplainProvenanceRecords.h
 *
 * Implementation of abstract class in ExplainProvenance.h for provenance using records
 *
 ***********************************************************************/

#pragma once

#include "ExplainProvenance.h"

#include <map>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

namespace souffle {

class ProvenanceInfo {
private:
    SouffleProgram& prog;

    std::map<std::pair<std::string, std::vector<RamDomain>>, RamDomain> valuesToLabel;
    std::map<std::pair<std::string, RamDomain>, std::vector<RamDomain>> labelToValue;
    std::map<std::pair<std::string, RamDomain>, std::vector<RamDomain>> labelToProof;
    std::map<std::string, std::vector<std::string>> info;
    std::map<std::pair<std::string, int>, std::string> rule;

public:
    ProvenanceInfo(SouffleProgram& p) : prog(p) {}

    void setup() {
        for (Relation* rel : prog.getAllRelations()) {
            std::string relName = rel->getName();

            for (auto& tuple : *rel) {
                RamDomain label;

                if (relName.find("-@output") != std::string::npos) {
                    std::vector<RamDomain> tuple_elements;
                    tuple >> label;

                    // construct tuple elements
                    for (size_t i = 1; i < tuple.size(); i++) {
                        if (*(rel->getAttrType(i)) == 'i' || *(rel->getAttrType(i)) == 'r') {
                            RamDomain n;
                            tuple >> n;
                            tuple_elements.push_back(n);
                        } else if (*(rel->getAttrType(i)) == 's') {
                            std::string s;
                            tuple >> s;
                            auto n = prog.getSymbolTable().lookupExisting(s.c_str());
                            tuple_elements.push_back(n);
                        }
                    }

                    // insert into maps
                    valuesToLabel.insert({std::make_pair(rel->getName(), tuple_elements), label});
                    labelToValue.insert({std::make_pair(rel->getName(), label), tuple_elements});
                } else if (relName.find("-@provenance-") != std::string::npos) {
                    std::vector<RamDomain> refs;
                    tuple >> label;

                    // construct vector of proof references
                    for (size_t i = 1; i < tuple.size(); i++) {
                        if (*(rel->getAttrType(i)) == 'i' || *(rel->getAttrType(i)) == 'r') {
                            RamDomain n;
                            tuple >> n;
                            refs.push_back(n);
                        } else if (*(rel->getAttrType(i)) == 's') {
                            std::string s;
                            tuple >> s;
                            // insert placeholder to refs for negated tuples
                            refs.push_back(-1);
                        }
                    }

                    labelToProof.insert({std::make_pair(rel->getName(), label), refs});
                } else if (relName.find("-@info") != std::string::npos) {
                    std::vector<std::string> rels;
                    for (size_t i = 0; i < tuple.size() - 2; i++) {
                        std::string s;
                        tuple >> s;
                        rels.push_back(s);
                    }

                    // second last argument is original relation name
                    std::string relName;
                    tuple >> relName;

                    // last argument is representation of clause
                    std::string clauseRepr;
                    tuple >> clauseRepr;

                    // extract rule number from relation name
                    int ruleNum = std::stoi(split(rel->getName(), '-').back());

                    info.insert({rel->getName(), rels});
                    rule.insert({std::make_pair(relName, ruleNum), clauseRepr});
                }
            }
        }
    }

    RamDomain getLabel(std::string relName, std::vector<RamDomain> e) {
        auto key = std::make_pair(relName, e);

        if (valuesToLabel.find(key) != valuesToLabel.end()) {
            return valuesToLabel[key];
        } else {
            return -1;
        }
    }

    std::vector<RamDomain> getTuple(std::string relName, RamDomain l) {
        auto key = std::make_pair(relName, l);

        if (labelToValue.find(key) != labelToValue.end()) {
            return labelToValue[key];
        } else {
            return std::vector<RamDomain>();
        }
    }

    std::vector<RamDomain> getSubproofs(std::string relName, RamDomain l) {
        auto key = std::make_pair(relName, l);

        if (labelToProof.find(key) != labelToProof.end()) {
            return labelToProof[key];
        } else {
            return std::vector<RamDomain>();
        }
    }

    std::vector<std::string> getInfo(std::string relName) {
        assert(info.find(relName) != info.end());
        return info[relName];
    }

    std::string getRule(std::string relName, int ruleNum) {
        auto key = std::make_pair(relName, ruleNum);

        if (rule.find(key) != rule.end()) {
            return rule[key];
        } else {
            return std::string("no rule found");
        }
    }
};

class ExplainProvenanceRecords : public ExplainProvenance {
private:
    ProvenanceInfo provInfo;
    std::unique_ptr<TreeNode> root;

    void printRelationOutput(
            const SymbolMask& symMask, const IODirectives& ioDir, const Relation& rel) override {
        WriteCoutCSVFactory().getWriter(symMask, prog.getSymbolTable(), ioDir, false)->writeAll(rel);
    }

public:
    ExplainProvenanceRecords(SouffleProgram& p) : ExplainProvenance(p), provInfo(p) {
        setup();
    }

    void setup() override {
        provInfo.setup();
    }

    std::unique_ptr<TreeNode> explainSubproof(std::string relName, RamDomain label, size_t depth) override {
        bool isEDB = true;
        bool found = false;
        for (auto rel : prog.getAllRelations()) {
            if (rel->getName().find(relName) != std::string::npos) {
                found = true;
            }
            std::regex provRelName(relName + "-@provenance-[0-9]+", std::regex_constants::extended);
            if (std::regex_match(rel->getName(), provRelName)) {
                isEDB = false;
                break;
            }
        }

        // check that relation is in the program
        if (!found) {
            return std::make_unique<LeafNode>("Relation " + relName + " not found");
        }

        // if EDB relation, make a leaf node in the tree
        if (prog.getRelation(relName) != nullptr && isEDB) {
            auto subproof = provInfo.getTuple(relName + "-@output", label);

            // construct label
            std::stringstream tup;
            tup << join(numsToArgs(relName, subproof), ", ");
            std::string lab = relName + "(" + tup.str() + ")";

            // leaf node
            return std::make_unique<LeafNode>(lab);
        } else {
            if (depth > 1) {
                std::string internalRelName;

                // find correct relation
                for (auto rel : prog.getAllRelations()) {
                    if (rel->getName().find(relName + "-@provenance-") != std::string::npos) {
                        // if relation contains the correct tuple label
                        if (provInfo.getSubproofs(rel->getName(), label) != std::vector<RamDomain>()) {
                            // found the correct relation
                            internalRelName = rel->getName();
                            break;
                        }
                    }
                }

                // either fact or relation doesn't exist
                if (internalRelName == "") {
                    // if fact
                    auto tup = provInfo.getTuple(relName + "-@output", label);
                    if (tup != std::vector<RamDomain>()) {
                        // output leaf provenance node
                        std::stringstream tupleText;
                        tupleText << join(numsToArgs(relName, tup), ", ");
                        std::string lab = relName + "(" + tupleText.str() + ")";

                        // leaf node
                        return std::make_unique<LeafNode>(lab);
                    } else {
                        return std::make_unique<LeafNode>("Relation " + relName + " not found");
                    }
                }

                // label and rule number for current node
                auto subproof = provInfo.getTuple(relName + "-@output", label);

                // construct label
                std::stringstream tup;
                tup << join(numsToArgs(relName, subproof), ", ");
                std::string lab = relName + "(" + tup.str() + ")";
                auto ruleNum = split(internalRelName, '-').back();

                // internal node representing current value
                auto inner =
                        std::unique_ptr<InnerNode>(new InnerNode(lab, std::string("(R" + ruleNum + ")")));

                // key for info map
                std::string infoKey = relName + "-@info-" + ruleNum;

                // recursively add all provenance values for this value
                auto subproofInfo = provInfo.getInfo(infoKey);
                auto subproofLabels = provInfo.getSubproofs(internalRelName, label);
                for (size_t i = 0; i < subproofInfo.size(); i++) {
                    auto rel = subproofInfo[i];
                    auto newLab = subproofLabels[i];

                    if (newLab == -1) {
                        inner->add_child(std::unique_ptr<TreeNode>(new LeafNode(rel)));
                    } else {
                        inner->add_child(explainSubproof(rel, newLab, depth - 1));
                    }
                }
                return std::move(inner);

                // add subproof label if depth limit is exceeded
            } else {
                std::string lab = "subproof " + relName + "(" + std::to_string(label) + ")";
                return std::make_unique<LeafNode>(lab);
            }
        }
    }

    std::unique_ptr<TreeNode> explain(
            std::string relName, std::vector<std::string> tuple, size_t depthLimit) override {
        auto lab = provInfo.getLabel(relName + "-@output", argsToNums(relName, tuple));
        if (lab == -1) {
            return std::make_unique<LeafNode>("Tuple not found");
        }

        return explainSubproof(relName, lab, depthLimit);
    }

    std::string getRule(std::string relName, size_t ruleNum) override {
        return provInfo.getRule(relName, ruleNum);
    }
};

}  // end of namespace souffle
