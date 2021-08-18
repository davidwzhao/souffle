/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Incremental.h
 *
 * Provenance interface for Souffle; works for compiler and interpreter
 *
 ***********************************************************************/

#pragma once

#include <csignal>
#include <iostream>
#include <regex>
#include <string>
#include <unistd.h>

#include "Explain.h"

#include "CompiledOptions.h"
#include "ProfileEvent.h"
#include "SouffleInterface.h"
#include "WriteStreamCSV.h"

namespace souffle {

class Incremental {
public:
    SouffleProgram& prog;
    ExplainConsole& explain;
    CmdOptions& opt;

    Incremental(SouffleProgram& prog, CmdOptions& opt, ExplainConsole& e) : prog(prog), opt(opt), currentEpoch(0), explain(e) {}

    /* Process a command, a return value of true indicates to continue, returning false indicates to break (if
     * the command is q/exit) */
    bool processCommand(std::string& commandLine) {
        std::vector<std::string> command = split(commandLine, ' ', 1);

        if (command.empty()) {
            return true;
        }

        if (command[0] == "insert") {
            std::pair<std::string, std::vector<std::string>> query;
            if (command.size() != 2) {
                printError("Usage: insert relation_name(\"<string element1>\", <number element2>, ...)\n");
                return true;
            }
            query = parseTuple(command[1]);
            insertTuple("diff_plus@_" + query.first, query.second);
        } else if (command[0] == "remove") {
            std::pair<std::string, std::vector<std::string>> query;
            if (command.size() != 2) {
                printError("Usage: remove relation_name(\"<string element1>\", <number element2>, ...)\n");
                return true;
            }
            query = parseTuple(command[1]);
            removeTuple("diff_minus@_" + query.first, query.second);
        } else if (command[0] == "commit") {
            // std::cout << "### BEGIN EPOCH " << currentEpoch << std::endl;
            currentEpoch++;
            commit();
            std::cout << "Commit done in epoch " << currentEpoch << "!\n";
        } else if (command[0] == "explain") {
            std::pair<std::string, std::vector<std::string>> query;
            if (command.size() != 2) {
                printError("Usage: explain relation_name(\"<string element1>\", <number element2>, ...)\n");
                return true;
            }
            query = parseTuple(command[1]);
            explain.printTree(explain.prov.explain(query.first, query.second, ExplainConfig::getExplainConfig().depthLimit));
        } else if (command[0] == "subproof") {
            std::pair<std::string, std::vector<std::string>> query;
            int label = -1;
            if (command.size() <= 1) {
                printError("Usage: subproof relation_name(<label>)\n");
                return true;
            }
            query = parseTuple(command[1]);
            label = std::stoi(query.second[0]);
            explain.printTree(explain.prov.explainSubproof(query.first, label, ExplainConfig::getExplainConfig().depthLimit));
        } else if (command[0] == "setdepth") {
            if (command.size() != 2) {
                printError("Usage: setdepth <depth>\n");
                return true;
            }
            try {
                ExplainConfig::getExplainConfig().depthLimit = std::stoi(command[1]);
            } catch (std::exception& e) {
                printError("<" + command[1] + "> is not a valid depth\n");
                return true;
            }
            printInfo("Depth is now " + std::to_string(ExplainConfig::getExplainConfig().depthLimit) + "\n");
        } else if (command[0] == "format") {
            if (command.size() == 2 && command[1] == "json") {
                ExplainConfig::getExplainConfig().json = true;
            } else if (command.size() == 2 && command[1] == "proof") {
                ExplainConfig::getExplainConfig().json = false;
            } else {
                printError("Usage: format <json|proof>\n");
            }
        } else if (command[0] == "exit" || command[0] == "q") {
            return false;
        } else {
            printError(
                    "\n----------\n"
                    "Commands:\n"
                    "----------\n"
                    "insert <relation>(<element1>, <element2>, ...): Inserts a new tuple\n"
                    "remove <relation>(<element1>, <element2>, ...): Removes an existing tuple\n"
                    "commit: Re-runs the Datalog program incrementally to apply changes\n"
                    "setdepth <depth>: Set a limit for printed derivation tree height\n"
                    "explain <relation>(<element1>, <element2>, ...): Prints derivation tree\n"
                    "subproof <relation>(<label>): Prints derivation tree for a subproof, label is\n"
                    "    generated if a derivation tree exceeds height limit\n"
                    "format <json|proof>: switch format between json and proof-trees\n"
                    "exit: Exits this interface\n\n");
        }

        return true;
    }

    /* The main explain call */
    void startIncremental() {
        printPrompt("Incremental is invoked.\n");

        while (true) {
            printPrompt("Enter command > ");
            std::string line = getInput();

            // a return value of false indicates that an exit/q command has been processed
            if (processCommand(line) == false) {
                break;
            }

            // print all tuples - just for debugging for now
            // prog.printAll();
        }
    }

private:
    int currentEpoch;

    void addTuple(const std::string& relName, const std::vector<std::string>& tup) {
        auto rel = prog.getRelation(relName);
        if (rel == nullptr) {
            printError("Relation " + relName + " not found!\n");
            return;
        }

        if (tup.size() != rel->getArity()) {
            printError("Tuple not of the right arity!\n");
            return;
        }

        tuple newTuple(rel);

        for (size_t i = 0; i < rel->getArity(); i++) {
            if (*rel->getAttrType(i) == 's') {
                // remove quotation marks
                if (tup[i].size() >= 2 && tup[i][0] == '"' && tup[i][tup[i].size() - 1] == '"') {
                    newTuple << tup[i].substr(1, tup[i].size() - 2);
                }
            } else {
                newTuple << (std::stoi(tup[i]));
            }
        }

        rel->insert(newTuple);

        /*
        // epoch number
        auto epochRel = prog.getRelation("+current_epoch");
        tuple epochNumber(epochRel);
        std::cout << "inserting new epoch: " << currentEpoch << std::endl;
        epochNumber << currentEpoch;
        epochRel->insert(epochNumber);
        */

        // run program until fixpoint
        // prog.run();
    }

    void commit() {
        if (opt.isProfiling()) {
            // std::cout << "profile filename: " << opt.getProfileName() << std::endl;
            ProfileEventSingleton::instance().setOutputFile(opt.getProfileName() + std::to_string(currentEpoch));
            ProfileEventSingleton::instance().clear();
        }
        std::vector<RamDomain> args;
        std::vector<RamDomain> ret;
        std::vector<bool> retErr;
        prog.executeSubroutine("update", args, ret, retErr);

        if (opt.isProfiling()) {
            ProfileEventSingleton::instance().stopTimer();
            ProfileEventSingleton::instance().dump();
        }
    }

    void insertTuple(const std::string& relName, std::vector<std::string> tup) {
        tup.push_back("0");
        // tup.push_back("0");
        tup.push_back("1");
        addTuple(relName, tup);
    }

    void removeTuple(const std::string& relName, std::vector<std::string> tup) {
        tup.push_back("0");
        // tup.push_back("1");
        tup.push_back("-1");
        addTuple(relName, tup);
    }

    /* Get input */
    std::string getInput() {
        std::string line;

        if (!getline(std::cin, line)) {
            // if EOF has been reached, quit
            line = "q";
        }

        return line;
    }

    /* Print a command prompt, disabled for non-terminal outputs */
    void printPrompt(const std::string& prompt) {
        if (!isatty(fileno(stdin))) {
            std::cout << "###" << std::endl << std::flush;
            return;
        }
        std::cout << prompt << std::endl << "###" << std::endl << std::flush;
    }

    /* Print any other information, disabled for non-terminal outputs */
    void printInfo(const std::string& info) {
        if (!isatty(fileno(stdin))) {
            return;
        }
        std::cout << info;
    }

    /* Print an error, such as a wrong command */
    void printError(const std::string& error) {
        std::cout << error;
    }

    /**
     * Parse tuple, split into relation name and values
     * @param str The string to parse, should be something like "R(x1, x2, x3, ...)"
     */
    std::pair<std::string, std::vector<std::string>> parseTuple(const std::string& str) {
        std::string relName;
        std::vector<std::string> args;

        // regex for matching tuples
        // values matches numbers or strings enclosed in quotation marks
        std::regex relRegex(
                "([a-zA-Z0-9_.-]*)[[:blank:]]*\\(([[:blank:]]*([0-9]+|\"[^\"]*\")([[:blank:]]*,[[:blank:]]*(-?["
                "0-"
                "9]+|\"[^\"]*\"))*)?\\)",
                std::regex_constants::extended);
        std::smatch relMatch;

        // first check that format matches correctly
        // and extract relation name
        if (!std::regex_match(str, relMatch, relRegex) || relMatch.size() < 3) {
            return std::make_pair(relName, args);
        }

        // set relation name
        relName = relMatch[1];

        // extract each argument
        std::string argsList = relMatch[2];
        std::smatch argsMatcher;
        std::regex argRegex(R"(-?[0-9]+|"[^"]*")", std::regex_constants::extended);

        while (std::regex_search(argsList, argsMatcher, argRegex)) {
            // match the start of the arguments
            std::string currentArg = argsMatcher[0];
            args.push_back(currentArg);

            // use the rest of the arguments
            argsList = argsMatcher.suffix().str();
        }

        return std::make_pair(relName, args);
    }

    /** utility function to split a string */
    inline std::vector<std::string> split(const std::string& s, char delim, int times = -1) {
        std::vector<std::string> v;
        std::stringstream ss(s);
        std::string item;

        while ((times > 0 || times <= -1) && std::getline(ss, item, delim)) {
            v.push_back(item);
            times--;
        }

        if (ss.peek() != EOF) {
            std::string remainder;
            std::getline(ss, remainder);
            v.push_back(remainder);
        }

        return v;
    }

};

inline void startIncremental(SouffleProgram& prog, CmdOptions& opt) {
    ExplainProvenanceImpl explainProv(prog, false);
    ExplainConsole e(explainProv);
    Incremental incr(prog, opt, e);
    incr.startIncremental();
}

}  // end of namespace souffle
