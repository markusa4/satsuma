// Copyright 2024 Markus Anders
// This file is part of satsuma 1.0.
// See LICENSE for extended copyright information.

#include "satsuma.h"
#include "parser.h"
#include <iostream>
#include <chrono>
#include <string>

typedef std::chrono::high_resolution_clock Clock;

dejavu::ir::refinement test_r;
dejavu::sgraph dej_test_graph;

void empty_hook(int, const int*, int, const int *) {}

int commandline_mode(int argc, char **argv) {

    std::string filename;
    bool entered_file = false;

    std::string out_filename;
    bool entered_out_file = false;

    bool struct_only = false;

    bool print = true;

    std::string write_auto_file_name;

    for (int i = 1; i < argc; ++i) {
        std::string arg = std::string(argv[i]);
        std::transform(arg.begin(), arg.end(), arg.begin(), ::toupper);
        std::replace(arg.begin(), arg.end(), '-', '_');

        if (arg == "__HELP" || arg == "_H") {
            std::clog << "Usage: satsuma [file] [options]" << std::endl;
            std::clog << "Computes symmetry breaking predicates for a CNF SAT formula." << std::endl;
            std::clog << "FILE is expected to be in DIMACS format (may also be piped)." << std::endl;
            std::clog << "Options:" << std::endl;
            std::clog << "    "  << std::left << std::setw(20) <<
            "--file [FILE]" << std::setw(16) <<
            "Input file in CNF format" << std::endl;
            std::clog << "    "  << std::left << std::setw(20) <<
                      "--out-file [FILE]" << std::setw(16) <<
                      "Output file in CNF format" << std::endl;
            return 0;
        } else if (arg == "__VERSION" || arg == "_V") {
            std::clog << SATSUMA_VERSION_MAJOR << "." << SATSUMA_VERSION_MINOR << std::endl;
            return 0;
        } else if ((arg == "__FILE") || (arg == "_F")) {
            if (i + 1 < argc) {
                i++;
                filename = argv[i];
                entered_file = true;
            } else {
                std::cerr << "--file option requires one argument." << std::endl;
                return 1;
            }
        } else if ((arg == "__OUT_FILE") || (arg == "_O")) {
            if (i + 1 < argc) {
                i++;
                out_filename = argv[i];
                entered_out_file = true;
            } else {
                std::cerr << "--out-file option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__STRUCT_ONLY") {
            struct_only = true;
        } else if (argv[i][0] != '-') {
            if(!entered_file) {
                filename = argv[i];
                entered_file = true;
            } else {
                std::cerr << "Extraneous file '" << argv[i] << "'. Only 1 file required." << std::endl;
                return 1;
            }
        } else  {
            std::cerr << "Invalid commandline option '" << argv[i] << "'." << std::endl;
            return 1;
        }
    }

    if(entered_file && !file_exists(filename)) {
        std::cerr << "File '" << filename << "' does not exist." << std::endl;
        return 1;
    }

    if(print) std::clog << "c ------------------------------------------------------------------" << std::endl;
    if(print) std::clog << "c       satsuma -- generator for symmetry breaking predicates" << std::endl;
    if(print) std::clog << "c       satsuma_version=" << SATSUMA_VERSION_MAJOR << "." << SATSUMA_VERSION_MINOR << ", ";
    if(print) std::clog << "dejavu_version=" << DEJAVU_VERSION_MAJOR << "." << DEJAVU_VERSION_MINOR <<
                        (DEJAVU_VERSION_IS_PREVIEW?"preview":"") << std::endl;
    if(print) std::clog << "c ------------------------------------------------------------------" << std::endl;

    if (!entered_file) {
        std::clog << "c no file was specified, reading instance from std::cin, (use --help for options)" << std::endl;
        //return 1;
    }

    // parsing
    if(print) std::clog << "c parsing " << filename;
    stopwatch sw;
    sw.start();
    cnf formula;
    parse_dimacs_to_cnf(filename, formula, entered_file);
    if(print) std::clog << " (" << sw.stop() << "ms)" << std::endl;
    std::clog << "c\t [cnf: #variables " << formula.n_variables() << " #clauses " << formula.n_clauses() << " #arr "
                     << formula.n_len() <<  "]"<<
                 std::endl;

    // call main algorithm
    satsuma::preprocessor satsuma_preprocessor;
    satsuma_preprocessor.set_struct_only(struct_only);
    if(entered_out_file) satsuma_preprocessor.output_file(out_filename);
    satsuma_preprocessor.preprocess(formula);

    return 0;
}

int main(int argc, char *argv[]) {
    return commandline_mode(argc, argv);
}
