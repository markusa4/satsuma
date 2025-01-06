// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_SATSUMA_H
#define SATSUMA_SATSUMA_H

#define SATSUMA_VERSION_MAJOR 1
#define SATSUMA_VERSION_MINOR 2

#include "dejavu/dejavu.h"
#include "cnf.h"
#include "cnf2wl.h"
#include "utility.h"
#include "group_analyzer.h"
#include "hypergraph.h"
#include "proof.h"

namespace satsuma {
    /**
     * \brief The satsuma preprocessor.
     *
     */
    class preprocessor {
        bool        entered_output_file = false;
        std::string output_filename     = "";

        // further modules
        std::ostream* log         = &std::clog; /**< logging */
        proof_veripb* my_proof    = nullptr;    /**< proof logging */
        profiler*     my_profiler = nullptr;    /**< profiling */

        // default configuration
        // modes
        bool struct_only = false;
        bool graph_only   = false;

        // general limits
        long graph_component_size_limit = 20000000; //< hard limit for component size

        // limits for special detection
        int row_orbit_limit        = 64;
        int row_column_orbit_limit = 64;
        int johnson_orbit_limit    = 64;

        // routines
        bool optimize_generators = true;
        bool preprocess_cnf      = false;
        bool preprocess_cnf_subsume = false;
        bool hypergraph_macros   = false;
        bool binary_clauses      = false;

        // limits for generator optimization
        int  opt_optimize_passes = 64;
        int  opt_addition_limit  = 196;
        int  opt_conjugate_limit = 256;
        bool opt_reopt = false;

        // options for breaking constraints
        int break_depth          = 512;

        long absolute_support_limit = 2 * 256 * 1024 * 1024; // we want no more than 2 GB worth of symmetries

        // dejavu settings
        bool dejavu_print        = false;
        bool dejavu_prefer_dfs   = false;
        int  dejavu_budget_limit = -1; // <0 means no limits\

        /**
            Compute a symmetry breaking predicate for the given formula.

            @param formula The given CNF formula.
        */
        void generate_symmetry_predicate(cnf& formula) {
            stopwatch sw;
            stopwatch total;

            // only output the graph used for symmetry detection
            if(graph_only) {
                group_analyzer symmetries;
                (*log) << "c\n";
                (*log) << "c output graph to '" << output_filename << "'";
                symmetries.compute_from_cnf(formula, true, output_filename);
                exit(0);
            }


            total.start();

            if(my_proof) my_proof->header(formula.n_clauses() + formula.n_duplicate_clauses_removed());

            hypergraph_wrapper hypergraph(formula);
            if(hypergraph_macros) {
                sw.start();
                (*log) << "c\n";
                (*log) << "c apply hyperstructure macros";
                hypergraph.hypergraph_reduction();
                const double t_hypergraph = sw.stop();
                (*log) << " (" << t_hypergraph << "ms)" << std::endl;
                if(my_profiler) my_profiler->add_result("hyperstructure_rewrite", t_hypergraph);
            }

            // transform the formula into a graph and apply color refinement to approximate orbits
            (*log) << "c\n";
            (*log) << "c make graph and approximate orbits";
            sw.start();
            group_analyzer symmetries(absolute_support_limit, graph_component_size_limit);
            //symmetries.compute_from_cnf(formula);
            symmetries.compute_from_hypergraph(hypergraph);
            hypergraph.clear(); // now that we have the graph, we don't need the corresponding hypergraph structure
            (*log) << std::endl << "c\t [group: #orbits ~= " << symmetries.n_orbits() << "]";
            const double t_approximate = sw.stop();
            (*log) << " (" << t_approximate << "ms)" << std::endl;
            if(my_profiler) my_profiler->add_result("approx_orbits", t_approximate);

            // now try to detect and break specific group actions
            (*log) << "c\n";
            (*log) << "c detect special group actions" << std::endl;
            sw.start();

            predicate sbp(formula.n_variables(), my_proof);

            // symmetries.detect_symmetric_action(formula, sbp);
            if (graph_component_size_limit <= 0 || 2*formula.n_variables() < graph_component_size_limit) {
                symmetries.detect_johnson_arity2(formula, sbp, johnson_orbit_limit);
                symmetries.detect_row_column_symmetry(formula, sbp, row_column_orbit_limit,
                                                         std::max(16*formula.n_variables(), 1024*1024*16));
                symmetries.detect_row_symmetry(formula, sbp, row_orbit_limit, std::max(16*formula.n_variables(), 1024*1024*16));
            } else {
            (*log) << "c\t exceeded limit" << std::endl;
            }

            const double t_detect_special = sw.stop();
            (*log) << "c\t (" << t_detect_special << "ms)" << std::endl;
            if(my_profiler) my_profiler->add_result("detect_special", t_detect_special);

            // next, apply dejavu on remainder, and break generators with generic strategy
            (*log) << "c\n";
            (*log) << "c detect symmetries on remainder" << std::endl;
            sw.start();
            formula.clear_db(); // don't need the DB anymore, so let's save memory
            symmetries.detect_symmetries_generic(dejavu_print, dejavu_prefer_dfs);
            (*log) << std::endl << "c\t [group: #symmetries " << symmetries.group_size() << " #generators " << symmetries.n_generators()
                       << "]";
            const double t_detect_generic = sw.stop();
            (*log) << " (" << t_detect_generic << "ms)" << std::endl;

            if(my_profiler) my_profiler->add_result("detect_generic", t_detect_generic);

            if(!struct_only && symmetries.n_generators() > 0) {
                if(binary_clauses) {
                    sw.start();
                    (*log) << "c\n";
                    (*log) << "c add binary clauses" << std::endl;
                    const int binary_clauses = symmetries.add_binary_clauses_no_schreier(formula, sbp);
                    const double t_break_binary = sw.stop();
                    (*log) << "c\t produced " << binary_clauses << " clauses" << " (" << t_break_binary << "ms)"
                              << std::endl;
                    if(my_profiler) my_profiler->add_result("break_binary", t_break_binary);
                }

                if(optimize_generators) {
                    sw.start();
                    (*log) << "c\n";
                    opt_conjugate_limit = std::max(opt_conjugate_limit, 3*5*symmetries.group_size().exponent / std::max(1, symmetries.n_orbits()/2));
                    (*log) << "c optimize generators (opt_passes="
                           << opt_optimize_passes << ", conjugate_limit=" << opt_conjugate_limit << ")" << std::endl;
                    symmetries.optimize_generators(opt_optimize_passes, opt_addition_limit, 
                                                   opt_conjugate_limit,
                                                   opt_reopt);
                    const double t_optimize_gens = sw.stop();
                    (*log) << "c\t " << "(" << t_optimize_gens << "ms)" << std::endl;
                    if(my_profiler) my_profiler->add_result("optimize_gens", t_optimize_gens);
                }
            }

            sw.start();
            (*log) << "c\n";
            (*log) << "c finalize break order and special generators" << std::endl;
            symmetries.finalize_break_order(formula, sbp);
            if(my_profiler) my_profiler->add_result("finalize_order", sw.stop());

            if(!struct_only && symmetries.n_generators() > 0) {
                sw.start();
                (*log) << "c\n";
                (*log) << "c add generic predicates (break_depth=" << break_depth << ")" << std::endl;
                const int constraints = symmetries.add_lex_leader_for_generators(formula, sbp, break_depth);
                const double t_break_generic = sw.stop();
                (*log) << "c\t added predicates for " << constraints << " generators (" << t_break_generic << "ms)" << std::endl;
                if(my_profiler) my_profiler->add_result("break_generic", t_break_generic);
            }

            (*log) << "c\n";
            (*log) << "c generation finished" << std::endl;
            (*log) << "c\t [sbp: #clauses " << sbp.n_clauses() << " #add_vars " << sbp.n_extra_variables() << "]" << std::endl;

            // output result
            sw.start();
            (*log) << "c\n";
            (*log) << "c write result";

            // file for output
            FILE* output_file;

            // buffer used for writing output
            const size_t buffer_size = 512*1024; // 512KB
            char  buffer[buffer_size];

            // choose whether to write to a file, or standard out
            if(entered_output_file) {
                (*log) << " to '" << output_filename << "'";
                output_file = fopen(output_filename.c_str(), "w");
                if(!output_file) terminate_with_error("unable to open output file '" + output_filename + "'");
            } else {
                output_file = stdout;
                (*log) << " to cout";
            }
            (*log) << std::endl;

            // attach buffer
            setvbuf(output_file, buffer, _IOFBF, buffer_size);

            // file header
            fprintf(output_file, "p cnf %d %d\n",formula.n_variables() + sbp.n_extra_variables(),
                                                  formula.n_clauses() + sbp.n_clauses());

            // write clauses
            satsuma_flockfile(output_file);
            formula.dimacs_output_clauses_unlocked(output_file);
            sbp.dimacs_output_clauses(output_file);
            satsuma_funlockfile(output_file);

            const long write_data = ftell(output_file); // how many bytes did we write?
            fclose(output_file);
            (*log) << "c \twritten " << write_data / 1000000.0 << "MB";
            const double t_output = sw.stop();
            (*log) << " (" << t_output << "ms)" << std::endl;

            if(my_profiler) my_profiler->add_result("output", t_output);
        }

    public:
        void set_struct_only(bool use_only_struct) {
            struct_only = use_only_struct;
        }

        void set_graph_only(bool use_only_struct) {
            graph_only = use_only_struct;
        }

        void set_optimize_generators(bool use_optimize_generators) {
            optimize_generators = use_optimize_generators;
        }

        void output_file(std::string& outfile) {
            output_filename = outfile;
            entered_output_file = true;
        }

        int get_row_orbit_limit() const {
            return row_orbit_limit;
        }

        void set_row_orbit_limit(int rowOrbitLimit) {
            row_orbit_limit = rowOrbitLimit;
        }

        int get_row_column_orbit_limit() const {
            return row_column_orbit_limit;
        }

        void set_row_column_orbit_limit(int rowColumnOrbitLimit) {
            row_column_orbit_limit = rowColumnOrbitLimit;
        }

        int get_johnson_orbit_limit() const {
            return johnson_orbit_limit;
        }

        void set_johnson_orbit_limit(int johnsonOrbitLimit) {
            johnson_orbit_limit = johnsonOrbitLimit;
        }

        int get_break_depth() const {
            return break_depth;
        }

        void set_break_depth(int breakDepth) {
            break_depth = breakDepth;
        }

        void set_opt_passes(int passes) {
            opt_optimize_passes = passes;
        }

        void set_opt_conjugations(int conjugations) {
            opt_conjugate_limit = conjugations;
        }

        void set_opt_random(int random) {
            opt_addition_limit = random;
        }

        void set_opt_reopt(bool reopt) {
            opt_reopt = reopt;
        }

        void set_dejavu_print(bool print) {
            dejavu_print = print;
        }

        void set_dejavu_prefer_dfs(bool prefer_dfs) {
            dejavu_prefer_dfs = prefer_dfs;
        }

        void set_preprocess_cnf_subsume(bool preprocessCNFsubsume) {
            preprocess_cnf_subsume = preprocessCNFsubsume;
        }


        void set_preprocess_cnf(bool preprocessCNF) {
            preprocess_cnf = preprocessCNF;
        }

        void set_hypergraph_macros(bool hypergraphMacros) {
            hypergraph_macros = hypergraphMacros;
        }

        void set_binary_clauses(bool binaryClauses) {
            binary_clauses = binaryClauses;
        }

        void set_proof(proof_veripb* my_proof = nullptr) {
            this->my_proof = my_proof;
        }

        void set_profiler(profiler* my_profiler = nullptr) {
            this->my_profiler = my_profiler;
        }

        void set_log_output(std::ostream* new_logout) {
            if(new_logout == nullptr) terminate_with_error("log output can not be nullptr");
            log = new_logout;
        }

        void preprocess(cnf2wl& formula) {
            stopwatch sw;

            // apply rudimentary, symmetry-preserving CNF preprocessing
            if(preprocess_cnf) {
                (*log) << "c\n";
                (*log) << "c preprocess cnf" << std::endl;
                sw.start();

                // propagate unit literals
                int unit_propagations = formula.propagate();

                // collect pure literals
                std::vector<int> pure_literals;
                formula.mark_literal_uses();
                for(int i = 0; i < formula.n_variables(); ++i) {
                    const int pos_lit = 1 + i;
                    const int neg_lit = -pos_lit;
                    if(formula.assigned(pos_lit) == 0) {
                        if(formula.is_literal_marked_used(pos_lit) && !formula.is_literal_marked_used(neg_lit)) {
                            pure_literals.push_back(pos_lit);
                        }
                        if(formula.is_literal_marked_used(neg_lit) && !formula.is_literal_marked_used(pos_lit)) {
                            pure_literals.push_back(neg_lit);
                        }
                    }
                }

                // propagate one round of pure literals
                const int pure_literal_num = pure_literals.size();
                for(const auto lit : pure_literals) {
                    formula.assign_literal(lit);
                }

                // propagate unit again
                unit_propagations += formula.propagate();

                // subsumption
                int subsumed = 0;
                if(preprocess_cnf_subsume) subsumed = formula.mark_subsumed_clauses();
                const double t_unit = sw.stop();
                if(my_profiler) my_profiler->add_result("unit", t_unit);
                (*log) << "c\t -units=" << unit_propagations << ", -pures=" << pure_literal_num << ", -subsumed=" << subsumed << " (" << t_unit << "ms)" << std::endl;
            }

            // generate symmetry breaking predicates
            constexpr bool keep_original_order = true;

            (*log) << "c\n";
            (*log) << "c make clause database (keep_order=" << keep_original_order << ")";
            sw.start();
            cnf formula_db;
            formula_db.read_from_cnf2wl(formula, keep_original_order);
            formula.clear();
            const double t_clause_db = sw.stop();
            if(my_profiler) my_profiler->add_result("clause_db", t_clause_db);
            (*log) << " (" << t_clause_db << "ms)";
            (*log) << std::endl;
            generate_symmetry_predicate(formula_db);
        }
    };
}

#endif //SATSUMA_SATSUMA_H
