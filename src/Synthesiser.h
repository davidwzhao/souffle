/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Synthesiser.h
 *
 * Declares synthesiser classes to synthesise C++ code from a RAM program.
 *
 ***********************************************************************/

#pragma once

#include "RamProgram.h"
#include "RamRelation.h"
#include "SymbolTable.h"

#include "RamStatement.h"

#include <ostream>
#include <string>
#include <vector>

namespace souffle {

/**
 * A RAM synthesiser: synthesises a C++ program from a RAM program.
 */
class Synthesiser {
private:
    /** An optional stream to print logging information to an output stream */
    std::ostream* report;

    /** compile command */
    std::string compileCmd;

public:
    /**
     * Updates logging stream
     */
    void setReportTarget(std::ostream& report) {
        this->report = &report;
    }

public:
    /** A simple constructor */
    Synthesiser(const std::string& compileCmd) : report(nullptr), compileCmd(compileCmd) {}

    /**
     * Generates the code for the given ram statement.The target file
     * name is either set by the corresponding member field or will
     * be determined randomly. The chosen file-name will be returned.
     */
    std::string generateCode(const SymbolTable& symTable, const RamProgram& prog,
            const std::string& filename = "", const int index = -1) const;

    /**
     * Compiles the given statement to a binary file. The target file
     * name is either set by the corresponding member field or will
     * be determined randomly. The chosen file-name will be returned.
     * Note that this uses the generateCode method for code generation.
     */
    std::string compileToBinary(const SymbolTable& symTable, const RamProgram& prog,
            const std::string& filename = "", const int index = -1) const;

    /**
     * Compiles the given statement to a binary file. The target file
     * name is either set by the corresponding member field or will
     * be determined randomly. The environment after execution will be returned.
     * Note that this uses the compileToBinary method for code compilation.
     */
    std::string executeBinary(const SymbolTable& symTable, const RamProgram& prog,
            const std::string& filename = "", const int index = -1) const;
};

}  // end of namespace souffle
