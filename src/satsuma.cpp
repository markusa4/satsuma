// Copyright 2026 Markus Anders
// This file is part of satsuma 1.4.
// See LICENSE for extended copyright information.

#include "satsuma.h"
#include "parser.h"
#include "knf_parser.h"
#include "graph_parser.h"
#include "proof.h"
#include "symmetries.h"
#include <iostream>
#include <chrono>
#include <string>

typedef std::chrono::high_resolution_clock Clock;

dejavu::ir::refinement test_r;
dejavu::sgraph dej_test_graph;

void empty_hook(int, const int*, int, const int *) {}

void print_help() {
    std::clog << "Satsuma has two modes:\n\n";
    std::clog << "     satsuma " << console_orange << "fix" << console_neutral << " [<dimacs>] [<options>] (iterative fixing)\n";
    std::clog << "     satsuma " << console_orange << "lex" << console_neutral <<" [<dimacs>] [<options>] (lex constraints)" << std::endl;
    std::clog << "\n";
    std::clog << "'fix' simplifies the CNF using symmetry" << std::endl;
    std::clog << "'lex' computes lex-leader symmetry breaking constraints" << std::endl;
    std::clog << "\n";
    std::clog << "Options:" << std::endl;
    std::clog << "\n";
    std::clog << "   "  << std::left << std::setw(23) <<
        "--file [FILE]" << std::setw(16) <<
        "Input file in CNF format" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--out-file [FILE]" << std::setw(16) <<
        "Output file in CNF format" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--proof-file [FILE]" << std::setw(16) <<
        "Proof file in SR or VeriPB format" << std::endl;
    std::clog << "\n";
    std::clog << "   "  << std::left << std::setw(23) <<
        "--dejavu-print" << std::setw(16) <<
        "Print progress of dejavu" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--dejavu-prefer-dfs" << std::setw(16) <<
        "Makes dejavu prefer depth-first search" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--output-graph-file" << std::setw(16) <<
        "Outputs the model graph in DIMACS" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--input-graph-file" << std::setw(16) <<
        "Uses the graph in DIMACS format as the model graph" << std::endl;
    std::clog << "\n";
    std::clog << "   "  << std::left << std::setw(23) <<
        "--opt" << std::setw(16) <<
        "Optimize generators" << std::endl;
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
    std::clog << "\n";
    std::clog << "   "  << std::left << std::setw(23) <<
        "--break-depth [N]" << std::setw(16) <<
        "Limits generic breaking constraints to depth n (lex)" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--preprocess-cnf" << std::setw(16) <<
        "Preprocess before symmetry breaking (lex)" << std::endl;
    std::clog << "   "  << std::left << std::setw(23) <<
        "--schreier-cuts" << std::setw(16) <<
        "Use the Schreier cut heuristic (lex)" << std::endl;
}


int commandline_mode(int argc, char **argv) {
    std::string filename;
    bool entered_file = false;
    read_type  file_type    = CNF;
    proof_type proof_format = SR;

    std::string out_filename;
    std::string input_graph_file;
    bool entered_out_file = false;

    bool use_proof_logging = false;
    std::string proof_filename;

    bool use_profiling     = true;

    bool print = true;
    empty_stream no_log;
    satsuma::preprocessor satsuma_preprocessor;

    std::string write_auto_file_name;
    if (argc > 1 && std::string(argv[1]) == "fix") {
        satsuma_preprocessor.set_orbitopal_fixing(true);
        satsuma_preprocessor.set_orbitopal_fixing_only(true);
        satsuma_preprocessor.set_schreier_fixing(true);
        satsuma_preprocessor.set_negation_fixing(true);
        satsuma_preprocessor.set_reorder(true);
        satsuma_preprocessor.set_reorder_cliquer(true);
        satsuma_preprocessor.set_iterate(true);
        satsuma_preprocessor.set_preprocess_cnf_unit(true);
        satsuma_preprocessor.set_preprocess_cnf_pure(true);
    }  else if(argc > 1 && (std::string(argv[1]) == "--help" || 
                            std::string(argv[1]) == "-h")) {
        print_help();
        return 0;
    } else if(argc <= 1 || std::string(argv[1]) != "lex") {
        std::clog << "Satsuma has two modes:\n\n";
        std::clog << "     satsuma " << console_orange << "fix" << console_neutral << " [<dimacs>] [<options>] (iterative fixing)\n";
        std::clog << "     satsuma " << console_orange << "lex" << console_neutral <<" [<dimacs>] [<options>] (lex constraints)" << std::endl;
        std::clog << "\nConsult satsuma --help for more options.";
        return 0;
    }

    satsuma_preprocessor.set_log_output(&no_log);
    for (int i = 2; i < argc; ++i) {
        std::string arg = std::string(argv[i]);
        std::transform(arg.begin(), arg.end(), arg.begin(), ::toupper);
        std::replace(arg.begin(), arg.end(), '-', '_');

        if (arg == "__HELP" || arg == "_H") {
            print_help();
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
        } else if ((arg == "__OUTPUT_GRAPH_FILE") || (arg == "_G")) {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_output_graph_file(argv[i]);
            } else {
                std::cerr << "--graph-file option requires one argument." << std::endl;
                return 1;
            }
        } else if ((arg == "__INPUT_GRAPH_FILE") || (arg == "_M")) {
            if (i + 1 < argc) {
                i++;
                input_graph_file = argv[i];
            } else {
                std::cerr << "--graph-file option requires one argument." << std::endl;
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
        } else if (arg == "__COMPONENT_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_component_size_limit(atoi(argv[i]));
            } else {
                std::cerr << "--component-limit option requires one argument." << std::endl;
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
            std::clog << "The design of the main algorithm is based on the following publications:\n" << std::endl;
            std::clog << "\t »Satsuma: Structure-based Symmetry Breaking in SAT« (SAT '24)\n\t  by Markus Anders, Sofia Brenner, Gaurav Rattan\n" << std::endl;
            std::clog << "\t »Algorithms Transcending the SAT-Symmetry Interface« (SAT '23)\n\t  by Markus Anders, Mate Soos, Pascal Schweitzer\n" << std::endl;
            std::clog << "\t »SAT Preprocessors and Symmetry« (SAT '22)\n\t  by Markus Anders" << std::endl;

            std::clog << "\nThe fixing algorithm and SR proof-logging is described in:\n" << std::endl;
            std::clog << "\t »Simplify, Order, Break, Repeat« (SAT '26)\n\t  by Markus Anders, Cayden Codel, Marijn J.H. Heule\n" << std::endl;
            std::clog << "\t »Orbitopal Fixing in SAT« (TACAS '26)\n\t  by Markus Anders, Cayden Codel, Marijn J.H. Heule" << std::endl;

            std::clog << "\nVeriPB proof-logging is described in:\n" << std::endl;
            std::clog << "\t »Faster Certified Symmetry Breaking using Orders with Auxiliary Variables« (AAAI '26)\n\t by Markus Anders, Bart Bogaerts, Benjamin Bogø, Arthur Gontier,\n\t    Wietze Koops, Ciaran McCreesh, Magnus Myreen, Jakob Nordström,\n\t    Andy Oertel, Adrian Rebola-Pardo, Yong Kiam Tan\n" << std::endl;

            return 0;
        } else if (arg == "__JOHNSON_ORBIT_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_johnson_orbit_limit(atoi(argv[i]));
            } else {
                std::cerr << "--johnson-orbit-limit option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__SPARSE_MODEL_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_sparse_model_budget(std::stoull(argv[i]));
            } else {
                std::cerr << "--sparse-model-limit option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__DENSE_MODEL_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_dense_model_budget(std::stoull(argv[i]));
            } else {
                std::cerr << "--dense-model-limit option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__FULL_SKIP_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_full_skip_limit(std::stoull(argv[i]));
            } else {
                std::cerr << "--full-skip-limit option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__ORDER_MODEL_LIMIT") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_order_model_budget(std::stoull(argv[i]));
            } else {
                std::cerr << "--order-model-limit option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__PROOF_DENSE_CROSSOVER") {
            if (i + 1 < argc) {
                i++;
                satsuma_preprocessor.set_proof_dense_crossover(atoi(argv[i]));
            } else {
                std::cerr << "--proof-dense-crossover option requires one argument." << std::endl;
                return 1;
            }
        } else if (arg == "__PROOF_SPARSE_RUP") {
            satsuma_preprocessor.set_proof_sparse_pol(false);
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
        } else if (arg == "__OPT") {
            satsuma_preprocessor.set_optimize_generators(true);
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
        } else if(arg == "__PREPROCESS_CNF_UNIT") {
            satsuma_preprocessor.set_preprocess_cnf_unit(true);
        } else if(arg == "__PREPROCESS_CNF_EQ") {
            satsuma_preprocessor.set_preprocess_cnf_eq(true);
        } else if(arg == "__PREPROCESS_CNF_PURE") {
            satsuma_preprocessor.set_preprocess_cnf_pure(true);
        } else if(arg == "__PREPROCESS_CNF_SUBSUME") {
            satsuma_preprocessor.set_preprocess_cnf_subsume(true);
        } else if(arg == "__HYPERGRAPH_MACROS") {
            satsuma_preprocessor.set_hypergraph_macros(true);
        } else if(arg == "__NO_HYPERGRAPH_MACROS") {
            satsuma_preprocessor.set_hypergraph_macros(false);
        } else if((arg == "__BINARY_CLAUSES") || (arg == "__SCHREIER_CUTS")) {
            satsuma_preprocessor.set_binary_clauses(true);
        } else if((arg == "__ORBITOPAL_FIXING")) {
            satsuma_preprocessor.set_orbitopal_fixing(true);
            satsuma_preprocessor.set_orbitopal_fixing_only(true);
        } else if((arg == "__SCHREIER_FIXING")) {
            satsuma_preprocessor.set_schreier_fixing(true);
            satsuma_preprocessor.set_orbitopal_fixing_only(true);
        } else if((arg == "__NEGATION_FIXING")) {
            satsuma_preprocessor.set_negation_fixing(true);
            satsuma_preprocessor.set_orbitopal_fixing_only(true);
        } else if((arg == "__FIXING")) {
            satsuma_preprocessor.set_orbitopal_fixing(true);
            satsuma_preprocessor.set_orbitopal_fixing_only(true);
            satsuma_preprocessor.set_schreier_fixing(true);
            satsuma_preprocessor.set_negation_fixing(true);
        } else if((arg == "__FIX_AND_CUT")) {
            satsuma_preprocessor.set_orbitopal_fixing(true);
            satsuma_preprocessor.set_orbitopal_fixing_only(true);
            satsuma_preprocessor.set_schreier_fixing(true);
            satsuma_preprocessor.set_negation_fixing(true);
            satsuma_preprocessor.set_reorder(true);
            satsuma_preprocessor.set_reorder_cliquer(true);
            satsuma_preprocessor.set_iterate(true);
            satsuma_preprocessor.set_preprocess_cnf_unit(true);
        } else if((arg == "__ITERATE")) {
            satsuma_preprocessor.set_iterate(true);
        } else if((arg == "__USE_FIRST_LIT")) {
            satsuma_preprocessor.set_order_first(true);
        } else if((arg == "__REORDER")) {
            satsuma_preprocessor.set_reorder(true);
        } else if((arg == "__CLIQUER")) {
            satsuma_preprocessor.set_reorder_cliquer(true);
        } else if (arg == "__STRUCT_ONLY") {
            satsuma_preprocessor.set_struct_only(true);
        } else if (arg == "__CNF") {
            file_type = CNF;
        } else if (arg == "__KNF") {
            file_type = KNF;
        } else if (arg == "__PB") {
            file_type = OPB;
        } else if (arg == "__SR") {
            proof_format = SR;
        } else if (arg == "__VERIPB") {
            proof_format = VERIPB;
        } else if (arg == "__BSR") {
            proof_format = BINARY_SR;
        } else if (arg == "__ADD_REDUCED_AS_UNIT") {
            satsuma_preprocessor.set_add_reduced_as_unit(true);
        } else if (arg == "__SILENT") {
            satsuma_preprocessor.set_log_output(&no_log);
            print = false;
        } else if (arg == "__VERBOSE") {
            satsuma_preprocessor.set_log_output(&std::clog);
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

    if(print) std::clog << std::setprecision(2) << std::fixed;
    if(print) std::clog << "c ┌────────────────────────────────────────────────────────────────┐\n";
    if(print) std::clog << "c │      satsuma -- a symmetry preprocessor for SAT                │\n";
    if(print) std::clog << "c │      satsuma_version=" << SATSUMA_VERSION_MAJOR << "." << SATSUMA_VERSION_MINOR << ", ";
    if(print) std::clog << "dejavu_version=" << DEJAVU_VERSION_MAJOR << "." << DEJAVU_VERSION_MINOR <<
                        (DEJAVU_VERSION_IS_PREVIEW?"preview":"") << "                   │\n";
    if(print) std::clog << "c │      (c) 2024-2026 Markus Anders                               │\n";
    if(print && use_proof_logging && proof_format == VERIPB) 
              std::clog << "c │          with proof-logging code by Wietze Koops               │\n";
    if(print) std::clog << "c │          see --authors for more information                    │\n";
    if(print) std::clog << "c └────────────────────────────────────────────────────────────────┘" << std::endl;

    if (!entered_file) {
        if(print) std::clog << "c no file specified, reading from stdin, (use --help for options)" << std::endl;
        //return 1;
    }

    // profiling
    satsuma::tracker  track;
    if(use_profiling) satsuma_preprocessor.set_tracker(&track);
    track.h_silent = !print;


    track.update_routine(PARSE);
    // parsing
    if(print) std::clog << "c parse '" << filename << "', expecting " 
                        << (file_type==CNF?"cnf":file_type==KNF?"knf":"opb");

    stopwatch sw;
    sw.start();
    cnf2wl formula;
    pbf    formula_pb;
    const double read_mb = file_type==CNF?parse_dimacs_to_cnf2wl(filename, formula,    entered_file): 
                           file_type==KNF?parse_knf_to_pb_db(filename,  formula_pb, entered_file):
                                          0;
    if(print) std::clog << "\nc \tread " << read_mb << "MB ";

    dejavu::sgraph   model_graph;
    dejavu::coloring model_graph_coloring;
    int*             coloring = nullptr;
    if(input_graph_file != "") {
        if(print) std::clog << "\nc \nc parse '" << input_graph_file << "', expecting graph";
        const double read_mb = satsuma::parse_graph(input_graph_file, &model_graph, &coloring);
        if(print) std::clog << "\nc \tread " << read_mb << "MB ";
        model_graph.initialize_coloring(&model_graph_coloring, coloring);
        if(!coloring) free(coloring);
        satsuma_preprocessor.set_input_graph(&model_graph);
        satsuma_preprocessor.set_input_coloring(&model_graph_coloring);
    }

    if(print) std::clog << " (" << sw.stop() << "ms)" << std::endl;
    if(print) std::clog << "c\t [cnf: #vars "
                        << (file_type==CNF?formula.n_variables():formula_pb.n_variables())
                        << " #cls " << (file_type==CNF?formula.n_clauses():formula_pb.n_clauses())
                        << " #taut "
                        << (file_type==CNF?formula.n_redundant_clauses():formula_pb.n_duplicate_clauses_removed())
                        << " #dupl "
                        << (file_type==CNF?formula.n_redundant_literals():0)
                        << " #arr " << (file_type==CNF?formula.n_len():formula_pb.n_len()) <<  "]"<< std::endl;
    if(print && input_graph_file != "") std::clog 
                        << "c\t [graph: #v " << model_graph.v_size
                        << " #e " <<  model_graph.e_size / 2 
                        << " #c " <<  model_graph_coloring.cells << std::endl;

    // proof logging
    std::ofstream proof_file;
    proof my_proof(proof_file, formula.n_variables(), proof_format);
    if(use_proof_logging) {
        try {
            proof_file.open(proof_filename);
        } catch (...) {
            terminate_with_error("could not open proof file '" + proof_filename + "'");
        }
        satsuma_preprocessor.set_proof(&my_proof);
    }
    if(use_proof_logging && print) std::clog << "c output proof to '" << proof_filename << "'\n";

    // call main algorithm
    if(entered_out_file) satsuma_preprocessor.output_file(out_filename);
    if(file_type == CNF) {
        satsuma_preprocessor.preprocess(formula);
    } else {
        satsuma_preprocessor.preprocess(formula_pb, file_type == KNF);
    }

    // output profile
    //if(use_profiling && print) {
    if(print && use_profiling) {
        satsuma::console_split();
        track.print_stats();
        const double t_total = sw.stop();
        satsuma::console_split();
        track.print_profile(t_total);
        satsuma::console_split();
    }
    return 0;
}

int main(int argc, char *argv[]) {
    return commandline_mode(argc, argv);
}
