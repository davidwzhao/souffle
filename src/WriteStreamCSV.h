/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2014, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file WriteStreamCSV.h
 *
 ***********************************************************************/

#pragma once

#include "SymbolMask.h"
#include "SymbolTable.h"
#include "WriteStream.h"
#ifdef USE_LIBZ
#include "gzfstream.h"
#endif

#include <fstream>
#include <memory>
#include <ostream>
#include <string>

namespace souffle {

class WriteFileCSV : public WriteStream {
public:
    WriteFileCSV(const std::string& filename, const SymbolMask& symbolMask, const SymbolTable& symbolTable,
            std::string delimiter = "\t", const bool provenance = false)
            : WriteStream(symbolMask, symbolTable, provenance), delimiter(std::move(delimiter)),
              file(filename) {}

    ~WriteFileCSV() override = default;

protected:
    void writeNextTuple(const RamDomain* tuple) override {
        size_t arity = symbolMask.getArity();
        if (isProvenance) {
            arity -= 2;
        }

        if (arity == 0) {
            file << "()\n";
            return;
        }

        if (symbolMask.isSymbol(0)) {
            file << symbolTable.unsafeResolve(tuple[0]);
        } else {
            file << static_cast<int32_t>(tuple[0]);
        }
        for (size_t col = 1; col < arity; ++col) {
            file << delimiter;
            if (symbolMask.isSymbol(col)) {
                file << symbolTable.unsafeResolve(tuple[col]);
            } else {
                file << static_cast<int32_t>(tuple[col]);
            }
        }
        file << "\n";
    }

protected:
    const std::string delimiter;
    std::ofstream file;
};

#ifdef USE_LIBZ
class WriteGZipFileCSV : public WriteStream {
public:
    WriteGZipFileCSV(const std::string& filename, const SymbolMask& symbolMask,
            const SymbolTable& symbolTable, std::string delimiter = "\t", const bool provenance = false)
            : WriteStream(symbolMask, symbolTable, provenance), delimiter(std::move(delimiter)),
              file(filename) {}

    ~WriteGZipFileCSV() override = default;

protected:
    void writeNextTuple(const RamDomain* tuple) override {
        size_t arity = symbolMask.getArity();

        // do not print last two provenance columns if provenance
        if (isProvenance) {
            arity -= 2;
        }

        if (arity == 0) {
            file << "()\n";
            return;
        }

        if (symbolMask.isSymbol(0)) {
            file << symbolTable.unsafeResolve(tuple[0]);
        } else {
            file << static_cast<int32_t>(tuple[0]);
        }
        for (size_t col = 1; col < arity; ++col) {
            file << delimiter;
            if (symbolMask.isSymbol(col)) {
                file << symbolTable.unsafeResolve(tuple[col]);
            } else {
                file << static_cast<int32_t>(tuple[col]);
            }
        }
        file << "\n";
    }

    const std::string delimiter;
    gzfstream::ogzfstream file;
};
#endif

class WriteCoutCSV : public WriteStream {
public:
    WriteCoutCSV(const std::string& relationName, const SymbolMask& symbolMask,
            const SymbolTable& symbolTable, std::string delimiter = "\t", const bool provenance = false)
            : WriteStream(symbolMask, symbolTable, provenance), delimiter(std::move(delimiter)) {
        std::cout << "---------------\n" << relationName << "\n===============\n";
    }

    ~WriteCoutCSV() override {
        std::cout << "===============\n";
    }

protected:
    void writeNextTuple(const RamDomain* tuple) override {
        size_t arity = symbolMask.getArity();

        if (isProvenance) {
            arity -= 2;
        }

        if (arity == 0) {
            std::cout << "()\n";
            return;
        }

        if (symbolMask.isSymbol(0)) {
            std::cout << symbolTable.unsafeResolve(tuple[0]);
        } else {
            std::cout << static_cast<int32_t>(tuple[0]);
        }
        for (size_t col = 1; col < arity; ++col) {
            std::cout << delimiter;
            if (symbolMask.isSymbol(col)) {
                std::cout << symbolTable.unsafeResolve(tuple[col]);
            } else {
                std::cout << static_cast<int32_t>(tuple[col]);
            }
        }
        std::cout << "\n";
    }

    const std::string delimiter;
};

class WriteCSVFactory {
protected:
    std::string getDelimiter(const IODirectives& ioDirectives) {
        if (ioDirectives.has("delimiter")) {
            return ioDirectives.get("delimiter");
        }
        return "\t";
    }
};

class WriteFileCSVFactory : public WriteStreamFactory, public WriteCSVFactory {
public:
    std::unique_ptr<WriteStream> getWriter(const SymbolMask& symbolMask, const SymbolTable& symbolTable,
            const IODirectives& ioDirectives, const bool provenance) override {
        std::string delimiter = getDelimiter(ioDirectives);
#ifdef USE_LIBZ
        if (ioDirectives.has("compress")) {
            return std::unique_ptr<WriteGZipFileCSV>(new WriteGZipFileCSV(
                    ioDirectives.get("filename"), symbolMask, symbolTable, delimiter, provenance));
        }
#endif
        return std::unique_ptr<WriteFileCSV>(new WriteFileCSV(
                ioDirectives.get("filename"), symbolMask, symbolTable, delimiter, provenance));
    }
    const std::string& getName() const override {
        static const std::string name = "file";
        return name;
    }
    ~WriteFileCSVFactory() override = default;
};

class WriteCoutCSVFactory : public WriteStreamFactory, public WriteCSVFactory {
public:
    std::unique_ptr<WriteStream> getWriter(const SymbolMask& symbolMask, const SymbolTable& symbolTable,
            const IODirectives& ioDirectives, const bool provenance) override {
        std::string delimiter = getDelimiter(ioDirectives);
        return std::unique_ptr<WriteCoutCSV>(new WriteCoutCSV(
                ioDirectives.getRelationName(), symbolMask, symbolTable, delimiter, provenance));
    }
    const std::string& getName() const override {
        static const std::string name = "stdout";
        return name;
    }
    ~WriteCoutCSVFactory() override = default;
};

} /* namespace souffle */
