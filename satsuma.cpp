// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
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

    bool use_proof_logging = false;
    std::string proof_filename;

    bool use_profiling     = true;

    bool print = true;
    satsuma::preprocessor satsuma_preprocessor;
    std::clog << std::setprecision(2) << std::fixed;

    std::string write_auto_file_name;

    for (int i = 1; i < argc; ++i) {
        std::string arg = std::string(argv[i]);
        std::transform(arg.begin(), arg.end(), arg.begin(), ::toupper);
        std::replace(arg.begin(), arg.end(), '-', '_');

        if (arg == "__HELP" || arg == "_H") {
            std::clog << "Usage: satsuma [file] [options]" << std::endl;
            std::clog << "Computes symmetry breaking predicates for a CNF SAT formula." << std::endl;
            std::clog << "FILE is expected to be in DIMACS format (may also be piped)." << std::endl;
            std::clog << "\n";
            std::clog << "Options:" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                         "--file [FILE]" << std::setw(16) <<
                         "Input file in CNF format" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                         "--out-file [FILE]" << std::setw(16) <<
                         "Output file in CNF format" << std::endl;
            std::clog << "   -----------------------------------------------------------------------\n";
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--dejavu-print" << std::setw(16) <<
                      "Print progress of dejavu" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--dejavu-prefer-dfs" << std::setw(16) <<
                      "Makes dejavu prefer depth-first search" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--graph-only" << std::setw(16) <<
                      "Outputs the model graph in DIMACS" << std::endl;
            std::clog << "   -----------------------------------------------------------------------\n";
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--break-depth [N]" << std::setw(16) <<
                      "Limits generic breaking constraints to depth n" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--preprocess-cnf" << std::setw(16) <<
                      "Preprocess before symmetry breaking" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--binary-clauses" << std::setw(16) <<
                      "Use the binary clause heuristic" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--no-opt" << std::setw(16) <<
                      "Don't optimize generators" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--opt-passes [N]" << std::setw(16) <<
                      "Passes used in support optimization " << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--opt-conjugations [N]" << std::setw(16) <<
                      "Limit for conjugates added from generators" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--opt-random [N]" << std::setw(16) <<
                      "Maximum number of random generators added" << std::endl;
            std::clog << "   "  << std::left << std::setw(23) <<
                      "--opt-reopt" << std::setw(16) <<
                      "Optimizes generators twice" << std::endl;
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
        } else if (arg == "__BREAK_DEPTH") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_break_depth(atoi(argv[i]));
            } else {
                std::cerr << "--break-depth option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__ROW_ORBIT_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_row_orbit_limit(atoi(argv[i]));
            } else {
                std::cerr << "--row-orbit-limit option requires one argument." << std::endl;
                return 1;
            }
        }  else if (arg == "__ROW_COLUMN_ORBIT_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_row_column_orbit_limit(atoi(argv[i]));
            } else {
                std::cerr << "--row-orbit-limit option requires one argument." << std::endl;
                return 1;
            }
        }  else if (arg == "__PAPERS" || arg == "__AUTHOR" || arg == "__AUTHORS") {
            std::clog << "satsuma is based on the following publications:\n" << std::endl;
            std::clog << "\t »Satsuma: Structure-based Symmetry Breaking in SAT« (SAT '24)\n\t  by Markus Anders, Sofia Brenner, Gaurav Rattan\n" << std::endl;
            std::clog << "\t »Algorithms Transcending the SAT-Symmetry Interface« (SAT '23)\n\t  by Markus Anders, Mate Soos, Pascal Schweitzer\n" << std::endl;
            std::clog << "\t »SAT Preprocessors and Symmetry« (SAT '22)\n\t  by Markus Anders" << std::endl;

            return 0;
        } else if (arg == "__JOHNSON_ORBIT_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_johnson_orbit_limit(atoi(argv[i]));
            } else {
                std::cerr << "--johnson-orbit-limit option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__OPT_PASSES") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_opt_passes(atoi(argv[i]));
            } else {
                std::cerr << "--opt-passes option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__OPT_CONJUGATIONS") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_opt_conjugations(atoi(argv[i]));
            } else {
                std::cerr << "--opt-conjugations option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__OPT_RANDOM") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_opt_random(atoi(argv[i]));
            } else {
                std::cerr << "--opt-random option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__OPT_REOPT") {
            satsuma_preprocessor.set_opt_reopt(true);
        } else if (arg == "__DEJAVU_PRINT") {
            satsuma_preprocessor.set_dejavu_print(true);
        } else if (arg == "__DEJAVU_PREFER_DFS") {
            satsuma_preprocessor.set_dejavu_prefer_dfs(true);
        } else if (arg == "__NO_OPT") {
            satsuma_preprocessor.set_optimize_generators(false);
        } else if (arg == "__NO_LIMITS") {
            satsuma_preprocessor.set_dejavu_backtrack_limit(-1);
            satsuma_preprocessor.set_component_size_limit(-1);
            satsuma_preprocessor.set_absolute_support_limit(-1);
            satsuma_preprocessor.set_row_orbit_limit(-1);
            satsuma_preprocessor.set_row_column_orbit_limit(-1);
            satsuma_preprocessor.set_johnson_orbit_limit(-1);
            satsuma_preprocessor.set_split_limit(-1);
        } else if(arg == "__PREPROCESS_CNF") {
            satsuma_preprocessor.set_preprocess_cnf(true);
        } else if(arg == "__PREPROCESS_CNF_SUBSUME") {
            satsuma_preprocessor.set_preprocess_cnf_subsume(true);
        } else if(arg == "__HYPERGRAPH_MACROS") {
            satsuma_preprocessor.set_hypergraph_macros(true);
        } else if(arg == "__BINARY_CLAUSES") {
            satsuma_preprocessor.set_binary_clauses(true);
        } else if (arg == "__STRUCT_ONLY") {
            satsuma_preprocessor.set_struct_only(true);
        } else if (arg == "__GRAPH_ONLY") {
            satsuma_preprocessor.set_graph_only(true);
        } else if (arg == "__PROOF_FILE") {
            if (i + 1 < argc) {
                i++;
                if (!use_proof_logging) {
                    proof_filename = argv[i];
                    use_proof_logging = true;
                } else {
                    terminate_with_error("Extraneous file '" + std::string(argv[i]) + "'. Only 1 proof file possible.");
                }
            } else {
                terminate_with_error("--proof-file option requires one argument." );
            }
        } else if (arg == "__NO_PROFILE") {
            use_profiling     = false;
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
        std::cerr << "file '" << filename << "' does not exist" << std::endl;
        return 1;
    }

    if(print) std::clog << "c ┌────────────────────────────────────────────────────────────────┐\n";
    if(print) std::clog << "c │      satsuma -- a symmetry preprocessor for SAT                │\n";
    if(print) std::clog << "c │      satsuma_version=" << SATSUMA_VERSION_MAJOR << "." << SATSUMA_VERSION_MINOR << ", ";
    if(print) std::clog << "dejavu_version=" << DEJAVU_VERSION_MAJOR << "." << DEJAVU_VERSION_MINOR <<
                        (DEJAVU_VERSION_IS_PREVIEW?"preview":"") << "                   │\n";
    if(print) std::clog << "c │      (c) 2024-2025 Markus Anders                               │\n";
    if(print) std::clog << "c │      ...based on work with Sofia Brenner, Gaurav Rattan,       │\n" <<
                           "c │                            Mate Soos, Pascal Schweitzer,       │\n" << 
                           "c │                            Bart Bogaerts                       │\n";
    if(print) std::clog << "c └────────────────────────────────────────────────────────────────┘" << std::endl;

    if (!entered_file) {
        std::clog << "c no file specified, reading from stdin, (use --help for options)" << std::endl;
        //return 1;
    }

    // profiling
    profiler my_profiler;
    if(use_profiling) satsuma_preprocessor.set_profiler(&my_profiler);

    // proof logging
    std::ofstream proof_file;
    proof_veripb my_proof(proof_file);
    if(use_proof_logging) {
        try {
            proof_file.open(proof_filename);
        } catch (...) {
            terminate_with_error("could not open proof file '" + proof_filename + "'");
        }
        satsuma_preprocessor.set_proof(&my_proof);
    }

    // parsing
    if(print) std::clog << "c parse '" << filename << "'";
    stopwatch sw;
    sw.start();
    cnf2wl formula;
    parse_dimacs_to_cnf2wl(filename, formula, entered_file);
    const double t_parse = sw.stop();
    my_profiler.add_result("parse", t_parse);
    if(print) std::clog << " (" << sw.stop() << "ms)" << std::endl;
    std::clog << "c\t [cnf: #variables " << formula.n_variables() << " #clauses " << formula.n_clauses()
                     << " #redundant " << formula.n_redundant_clauses() << " #arr "
                     << formula.n_len() <<  "]"<< std::endl;

    if(use_proof_logging && print) std::clog << "c output proof to '" << proof_filename << "'\n";

    // call main algorithm
    if(entered_out_file) satsuma_preprocessor.output_file(out_filename);
    satsuma_preprocessor.preprocess(formula);

    // output profile
    if(use_profiling) {
        std::clog << "c ------------------------------------------------------------------\n";
        const double t_total = sw.stop();
        my_profiler.print_results(std::clog, t_total);
        std::clog << "c ------------------------------------------------------------------\n";
    }
    return 0;
}

int main(int argc, char *argv[]) {
    return commandline_mode(argc, argv);
}
