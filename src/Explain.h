/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2017, The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file Explain.h
 *
 * Provenance interface for Souffle; works for compiler and interpreter
 *
 ***********************************************************************/

#pragma once

#include "ExplainProvenanceRecords.h"
#include "ExplainProvenanceSLD.h"

#include <csignal>
#include <iostream>
#include <regex>
#include <string>
#include <ncurses.h>

#include "SouffleInterface.h"
#include "WriteStreamCSV.h"

#define MAX_TREE_HEIGHT 500
#define MAX_TREE_WIDTH 500

namespace souffle {

class Explain {
private:
    ExplainProvenance& prov;

    bool ncurses;
    WINDOW* treePad;
    WINDOW* queryWindow;
    int maxx, maxy;

    int depthLimit;

    // parse relation, split into relation name and values
    std::pair<std::string, std::vector<std::string>> parseRel(std::string rel) {
        // remove spaces
        rel.erase(std::remove(rel.begin(), rel.end(), ' '), rel.end());

        // remove last closing parenthesis
        if (rel.back() == ')') {
            rel.pop_back();
        }

        auto splitRel = split(rel, '(');
        std::string relName;
        if (splitRel.size() > 0) {
            relName = splitRel[0];
        }
        std::vector<std::string> args;

        if (splitRel.size() > 1) {
            args = split(splitRel[1], ',');
        }

        return std::make_pair(relName, args);
    }

    // initialise ncurses window
    WINDOW* makeQueryWindow() {
        WINDOW* w = newwin(3, maxx, maxy - 2, 0);
        wrefresh(w);
        return w;
    }

    // print provenance tree
    void printTree(std::unique_ptr<TreeNode> tree) {
        if (tree) {
            tree->place(0, 0);
            ScreenBuffer screenBuffer(tree->getWidth(), tree->getHeight());
            tree->render(screenBuffer);
            if (ncurses) {
                wprintw(treePad, screenBuffer.getString().c_str());
            } else {
                std::cout << screenBuffer.getString();
            }
        }
    }

    // print string
    void printStr(std::string s) {
        if (ncurses) {
            wprintw(treePad, s.c_str());
        } else {
            std::cout << s;
        }
    }

    // allow scrolling of provenance tree
    void scrollTree(int maxx, int maxy) {
        int x = 0;
        int y = 0;

        while (1) {
            int ch = wgetch(treePad);

            if (ch == KEY_LEFT) {
                if (x > 2) x -= 3;
            } else if (ch == KEY_RIGHT) {
                if (x < MAX_TREE_WIDTH - 3) x += 3;
            } else if (ch == KEY_UP) {
                if (y > 0) y -= 1;
            } else if (ch == KEY_DOWN) {
                if (y < MAX_TREE_HEIGHT - 1) y += 1;
            } else {
                break;
            }

            prefresh(treePad, y, x, 0, 0, maxy - 3, maxx - 1);
        }
    }

    // initialise ncurses window
    void initialiseWindow() {
        initscr();

        // get size of window
        getmaxyx(stdscr, maxy, maxx);

        // create windows for query and tree display
        queryWindow = makeQueryWindow();
        treePad = newpad(MAX_TREE_HEIGHT, MAX_TREE_WIDTH);

        keypad(treePad, true);
    }

public:
    Explain(ExplainProvenance& p, bool ncurses, int d = 4) : prov(p), ncurses(ncurses), depthLimit(d) {}

    void explain() {
        if (ncurses) {
            initialiseWindow();
            std::signal(SIGWINCH, NULL);
        }

        // process commands
        char buf[100];
        std::string line;

        while (1) {
            if (ncurses) {
                // reset command line on each loop
                werase(queryWindow);
                wrefresh(queryWindow);
                mvwprintw(queryWindow, 1, 0, "Enter command > ");
                curs_set(1);
                echo();

                // get next command
                wgetnstr(queryWindow, buf, 100);
                noecho();
                curs_set(0);
                line = buf;

                // reset tree display on each loop
                werase(treePad);
                prefresh(treePad, 0, 0, 0, 0, maxy - 3, maxx - 1);
            } else {
                std::cout << "Enter command > ";
                getline(std::cin, line);
            }

            std::vector<std::string> command = split(line, ' ', 1);

            if (command.size() == 0) {
                continue;
            }

            if (command[0] == "setdepth") {
                try {
                    depthLimit = std::stoi(command[1]);
                } catch (std::exception& e) {
                    printStr("Usage: setdepth <depth>\n");
                    continue;
                }
                printStr("Depth is now " + std::to_string(depthLimit) + "\n");
            } else if (command[0] == "explain") {
                std::pair<std::string, std::vector<std::string>> query;
                if (command.size() > 1) {
                    query = parseRel(command[1]);
                } else {
                    printStr("Usage: explain relation_name(<element1>, <element2>, ...)\n");
                    continue;
                }
                std::unique_ptr<TreeNode> t = prov.explain(query.first, query.second, depthLimit);
                printTree(std::move(t));
            } else if (command[0] == "subproof") {
                std::pair<std::string, std::vector<std::string>> query;
                int label = -1;
                if (command.size() > 1) {
                    query = parseRel(command[1]);
                    label = std::stoi(query.second[0]);
                } else {
                    printStr("Usage: subproof relation_name(<label>)\n");
                    continue;
                }
                std::unique_ptr<TreeNode> t = prov.explainSubproof(query.first, label, depthLimit);
                printTree(std::move(t));
            } else if (command[0] == "rule") {
                try {
                    auto query = split(command[1], ' ');
                    printStr(prov.getRule(query[0], std::stoi(query[1])) + "\n");
                } catch (std::exception& e) {
                    printStr("Usage: rule <rule number>\n");
                    continue;
                }
            } else if (command[0] == "printrel") {
                try {
                    printStr(prov.getRelationOutput(command[1]));
                } catch (std::exception& e) {
                    printStr("Usage: printrel <relation name>\n");
                    continue;
                }
            } else if (command[0] == "help") {
                printStr(
                        "\n----------\n"
                        "Commands:\n"
                        "----------\n"
                        "setdepth <depth>: Set a limit for printed derivation tree height\n"
                        "explain <relation>(<element1>, <element2>, ...): Prints derivation tree\n"
                        "subproof <relation>(<label>): Prints derivation tree for a subproof, label is "
                        "generated if a derivation tree exceeds height limit\n"
                        "rule <rule number>: Prints a rule\n"
                        "printrel <relation name>: Prints the tuples of a relation\n"
                        "exit: Exits this interface\n\n");
            } else if (command[0] == "exit") {
                printStr("Exiting explain\n");
                break;
            }

            // refresh treePad and allow scrolling
            if (ncurses) {
                prefresh(treePad, 0, 0, 0, 0, maxy - 3, maxx - 1);
                scrollTree(maxx, maxy);
            }
        }
        if (ncurses) {
            endwin();
        }
    }
};

inline void explain(SouffleProgram& prog, bool sld = true, bool ncurses = false) {
    std::cout << "Explain is invoked.\n";

    ExplainProvenance* prov;
    if (sld) {
        prov = new ExplainProvenanceSLD(prog);
    } else {
        prov = new ExplainProvenanceRecords(prog);
    }

    Explain exp(*prov, ncurses);
    exp.explain();

    if (prov) {
        delete prov;
    }
}

}  // end of namespace souffle
