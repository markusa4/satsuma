// Copyright 2026 Markus Anders
// This file is part of satsuma 1.3.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_SATSUMA_H
#define SATSUMA_SATSUMA_H

#define SATSUMA_VERSION_MAJOR 1
#define SATSUMA_VERSION_MINOR 3

#include "dejavu/ds.h"
#include "dejavu/dejavu.h"
#include "cnf.h"
#include "pbf.h"
#include "cnf2wl.h"
#include "utility.h"
#include "symmetries.h"
#include "hypergraph.h"
#include "proof.h"
#include "tracker.h"

namespace satsuma {
    /**
     * \brief The satsuma preprocessor.
     *
     */
    class preprocessor {
        // output file
        bool              entered_output_file   = false;
        std::string       output_filename       = "";
        std::string       output_graph_filename = "";
        dejavu::sgraph*   input_graph    = nullptr;
        dejavu::coloring* input_coloring = nullptr;

        // further modules
        std::ostream* log         = &std::clog; /**< logging */
        proof*        my_proof    = nullptr;    /**< proof logging */
        tracker*      track;

        // proof options 
        bool add_reduced_variables_as_unit = false; // will make sure that SAT solver prints assignment that satisfies 
                                                    // the original formula

        // modes
        bool struct_only = false;

        // general limits
        uint64_t computational_cost = 1;
        bool reached_limits = false;
        long graph_component_size_limit = 5000000; //< hard limit for component size
        long full_skip_limit            = -1; //< hard limit for component size 
        long schreier_domain_limit      = 50000;   //< hard limit for Schreier domains
        uint64_t total_cost_limit = 20000000000;   //< hard limit for Schreier domains

        // limits for special detection
        int row_orbit_limit        = 64;
        int row_column_orbit_limit = 64;
        int johnson_orbit_limit    = 64;
        long split_limit           = 1024 * 1024 * 16;

        // order limit
        long order_limit           = -1;

        // routines
        bool optimize_generators    = false;
        bool preprocess_cnf_unit    = false;
        bool preprocess_cnf_pure    = false;
        bool preprocess_cnf_subsume = false;
        bool preprocess_cnf_eq      = false;
        bool hypergraph_macros      = true;
        bool binary_clauses         = false;
        bool orbitopal_fixing       = false;
        bool schreier_fixing        = false;
        bool negation_fixing        = false;
        bool orbitopal_fixing_only  = false;
        bool iterate                = false;
        int  iteration_limit        = 128;
        bool reorder                = false;
        bool reorder_cliquer        = false;
        bool order_first_lit        = false;

        // limits for generator optimization
        int  opt_optimize_passes = 64;
        int  opt_addition_limit  = 196;
        int  opt_conjugate_limit = 256;
        bool opt_reopt           = false;

        // options for breaking constraints
        int break_depth          = 512;

        // dejavu settings
        bool dejavu_print           = false;
        bool dejavu_prefer_dfs      = false;
        int  dejavu_budget_limit    = -1;    // -1 means no limits
        int  dejavu_backtrack_limit = 64;
        //long absolute_support_limit = 2 * 256 * 1024 * 1024; // we want no more than 2 GB worth of symmetries
        long absolute_support_limit = 64 * 1024 * 1024; // we want no more than 2 GB worth of symmetries
        
        // limits for the predicate
        uint64_t dense_model_budget  = std::numeric_limits<uint64_t>::max();
        uint64_t order_model_budget  = std::numeric_limits<uint64_t>::max();
        uint64_t sparse_model_budget = std::numeric_limits<uint64_t>::max();

        // options for proof logging 
        int proof_dense_crossover = 64;
        bool proof_pol_log        = true;

        /**
            Compute a symmetry breaking predicate for the given formula.

            @param formula The given CNF formula.
        */
        void generate_symmetry_predicate(cnf& formula, predicate& sbp) {
            stopwatch sw;
            stopwatch total;

            total.start();


            // apply reductions based on viewing the formula as a hypergraph
            hypergraph_wrapper hypergraph(formula);
            if(hypergraph_macros) {
                //sw.start();
                if(track) track->force_print();
                if(track) track->update_routine(HYPERGRAPH);
                (*log) << "c \n";
                (*log) << "c apply hypergraph macros";
                hypergraph.hypergraph_reduction();
                track->add_to_metric(COST_SYM, 10*formula.n_total_clause_size() + formula.n_variables());
            }

            // transform the formula into a graph and apply color refinement to approximate orbits
            if(track) track->force_print();
            if(track) track->update_routine(REFINE);
            (*log) << "c \n";
            (*log) << "c make graph and approximate orbits";

            long reduce_absolute_limit = std::min((long) formula.n_variables() * 256 + formula.n_clauses(), 
                                                   absolute_support_limit);
            if(reduce_absolute_limit > 0) 
                reduce_absolute_limit = std::max(reduce_absolute_limit, (long) 12*1024*1024);

            long reduce_backtrack_limit = (formula.n_variables() < 32000)?dejavu_backtrack_limit:1;

            symmetries sym(reduce_absolute_limit, graph_component_size_limit, reduce_backtrack_limit, 
                           track);
            sym.set_reorder(reorder);
            sym.set_order_first(order_first_lit);
            sym.set_reorder_cliquer(reorder_cliquer);
            sym.set_orbitopal_fixing(orbitopal_fixing);
            sym.set_orbitopal_fixing_only(orbitopal_fixing_only);
            sym.set_log_output(log);
            if(input_graph == nullptr) 
                sym.compute_from_hypergraph(hypergraph, output_graph_filename != "", output_graph_filename);
            else
                sym.compute_from_model_graph(formula.n_variables(), input_graph, input_coloring);

            hypergraph.clear(); // now that we have the graph, we don't need the corresponding hypergraph structure
            (*log) << std::endl << "c\t [group: #orbits ~= " << sym.n_orbits() << "]";

            // now try to detect and break specific group actions
            (*log) << "c \n";
            (*log) << "c detect special group actions" << std::endl;
            if(track) track->force_print();
            if(track) track->update_routine(DETECT_SPECIAL);

            // symmetries.detect_symmetric_action(formula, sbp);
            if (graph_component_size_limit <= 0 || sym.get_graph_vertices() < graph_component_size_limit) {
                sym.detect_johnson_arity2(formula, sbp, johnson_orbit_limit);
                sym.detect_row_column_symmetry(formula, sbp, row_column_orbit_limit,
                                               std::max((long) 16*formula.n_variables(), split_limit));
                sym.detect_row_symmetry(formula, sbp, row_orbit_limit, 
                                               std::max((long) 16*formula.n_variables(), split_limit));
            } else {
                reached_limits = true;
                (*log) << "c \t exceeded limit" << std::endl;
            }

            // next, apply dejavu on remainder, and break generators with generic strategy
            (*log) << "c \n";
            (*log) << "c detect symmetries on remainder" << std::endl;
            if(track) track->force_print();
            if(track) track->update_routine(DETECT_GENERIC);
            if(!schreier_fixing) formula.clear_db(); // don't need the DB anymore, so let's save memory

            const bool skip_generic = orbitopal_fixing && iterate && sbp.n_clauses() > 1;

            if(!(orbitopal_fixing && !schreier_fixing && !negation_fixing) && !struct_only && !skip_generic) 
                sym.detect_symmetries_generic(dejavu_print, dejavu_prefer_dfs);
            else (*log) << "c \t(skipped)";
            (*log) << std::endl << "c \t[group: #symmetries " << sym.group_size() << " #gens " << sym.n_generators()
                       << "]";
            track->add_to_metric(COST_SYM, sym.get_refinement_cost() / 10);
            reached_limits = reached_limits || sym.get_reached_limits();

            if(sym.n_generators() > 0) {
                if(optimize_generators) {
                    if(track) track->force_print();
                    if(track) track->update_routine(OPTIMIZE);
                    (*log) << "c \n";
                    opt_conjugate_limit = 
                        std::max(opt_conjugate_limit, 3*5*sym.group_size().exponent / std::max(1, sym.n_orbits()/2));
                    (*log) << "c optimize generators (opt_passes="
                           << opt_optimize_passes << ", conjugate_limit=" << opt_conjugate_limit << ")" << std::endl;
                    sym.optimize_generators(opt_optimize_passes, opt_addition_limit, opt_conjugate_limit, opt_reopt);
                    const double t_optimize_gens = sw.stop();
                    (*log) << "c \t" << "(" << t_optimize_gens << "ms)" << std::endl;
                }

                if(orbitopal_fixing_only) {
                    sym.filter_to_unordered_generators(sbp);
                }

                if(negation_fixing) {
                    if(track) track->force_print();
                    if(track) track->update_routine(SCHREIER);
                    if(formula.n_variables() > schreier_domain_limit) sym.negation_fixing(sbp);
                    else sym.negation_fixing_schreier(sbp, total_cost_limit);
                    const double t_negation_fix = sw.stop();
                    (*log) << "c \t" << "(" << t_negation_fix << "ms)" << std::endl;
                }

                if(schreier_fixing) {
                    if(track) track->force_print();
                    if(track) track->update_routine(SCHREIER);
                    //sym.schreier_fixing(formula, sbp);
                    if(formula.n_variables() > schreier_domain_limit) sym.binary_fixing(formula, sbp);
                    else sym.fix_and_cut(sbp, formula, true, total_cost_limit);
                    const double t_schreier_fix = sw.stop();
                    (*log) << "c \t" << "(" << t_schreier_fix << "ms)" << std::endl;
                }

                if(binary_clauses) {
                    if(my_proof) terminate_with_error("binary clauses and proof-logging are currently incompatible");
                    if(track) track->force_print();
                    if(track) track->update_routine(SCHREIER);
                    (*log) << "c \n";
                    (*log) << "c add binary clauses" << std::endl;
                    int binary_clauses = 0;
                    //if(formula.n_variables() > schreier_domain_limit) 
                    binary_clauses = sym.add_binary_clauses_no_schreier(sbp);
                    //else                                              
                    //    binary_clauses = sym.schreier_cuts(sbp, formula, true);
                    const double t_break_binary = sw.stop();
                    (*log) << "c \t produced " << binary_clauses << " clauses" << " (" << t_break_binary << "ms)"
                              << std::endl;
                }
            }

            if(!orbitopal_fixing_only) {
                if(track) track->force_print();
                if(track) track->update_routine(ORDER);
                (*log) << "c \n";
                (*log) << "c finalize break order and special generators" << std::endl;
                if(!orbitopal_fixing_only) sym.finalize_break_order(formula, sbp);
            }

            if(!struct_only && sym.n_generators() > 0 && !orbitopal_fixing_only) {
                if(track) track->force_print();
                if(track) track->update_routine(BREAK);
                (*log) << "c \n";
                (*log) << "c add generic predicates (break_depth=" << break_depth << ")" << std::endl;
                const int constraints = sym.add_lex_leader_for_generators(formula, sbp, break_depth);
                (*log) << "c \tadded predicates for " << constraints << " generators" << std::endl;
            }

            reached_limits = reached_limits || sym.get_reached_limits();

            // deferred writing for proof logging
            sbp.write_all_deferred(order_limit);

            (*log) << "c \n";
            (*log) << "c iteration finished" << std::endl;
            (*log) << "c \t[group: #gens "  << sbp.get_generators() << " #avg_support " 
                                            << (1.0 * sbp.get_support()) / sbp.get_generators() << "]" << std::endl;
            (*log) << "c \t[sbp: #clauses " << sbp.n_clauses() << " #add_vars " 
                                            << sbp.n_extra_variables() << "]" << std::endl;
        }

        /**
            Compute a symmetry breaking predicate for the given formula.

            @param formula The given PB formula.
        */
        void generate_symmetry_predicate(pbf& formula, predicate& sbp) {
            stopwatch sw;
            stopwatch total;

            total.start();

            // transform the formula into a graph and apply color refinement to approximate orbits
            (*log) << "c \n";
            (*log) << "c make graph and approximate orbits";
            sw.start();
            symmetries sym(absolute_support_limit, graph_component_size_limit,
                           dejavu_backtrack_limit, track);
            sym.set_reorder(reorder);
            sym.set_order_first(order_first_lit);
            sym.set_log_output(log);
            sym.compute_from_pbf(formula);
            (*log) << std::endl << "c\t [group: #orbits ~= " << sym.n_orbits() << "]";
            const double t_approximate = sw.stop();
            (*log) << " (" << t_approximate << "ms)" << std::endl;

            // now try to detect and break specific group actions
            (*log) << "c \n";
            (*log) << "c detect special group actions" << std::endl;
            sw.start();

            // symmetries.detect_symmetric_action(formula, sbp);
            if (graph_component_size_limit <= 0 || 2*formula.n_variables() < graph_component_size_limit) {
                sym.detect_johnson_arity2(formula, sbp, johnson_orbit_limit);
                sym.detect_row_column_symmetry(formula, sbp, row_column_orbit_limit,
                                               std::max((long) 16*formula.n_variables(), split_limit));
                sym.detect_row_symmetry(formula, sbp, row_orbit_limit, 
                                        std::max((long) 16*formula.n_variables(), split_limit));
            } else {
                (*log) << "c \t exceeded limit" << std::endl;
            }

            const double t_detect_special = sw.stop();
            (*log) << "c \t (" << t_detect_special << "ms)" << std::endl;

            // next, apply dejavu on remainder, and break generators with generic strategy
            (*log) << "c \n";
            (*log) << "c detect symmetries on remainder" << std::endl;
            sw.start();
            //formula.clear_db(); // don't need the DB anymore, so let's save memory
            if(2*formula.n_variables() < graph_component_size_limit) { 
                sym.detect_symmetries_generic(dejavu_print, dejavu_prefer_dfs);
                (*log) << std::endl;
            }
            (*log) << "c \t [group: #symmetries " << sym.group_size() << " #generators " << sym.n_generators() << "]";
            const double t_detect_generic = sw.stop();
            (*log) << " (" << t_detect_generic << "ms)" << std::endl;


            if(!struct_only && sym.n_generators() > 0) {
                if(binary_clauses) {
                    if(my_proof) terminate_with_error("binary clauses and proof-logging are currently incompatible");
                    sw.start();
                    (*log) << "c \n";
                    (*log) << "c add binary clauses" << std::endl;
                    const int binary_clauses = sym.add_binary_clauses_no_schreier(sbp);
                    const double t_break_binary = sw.stop();
                    (*log) << "c \t produced " << binary_clauses << " clauses" << " (" << t_break_binary << "ms)"
                              << std::endl;
                }

                if(optimize_generators) {
                    sw.start();
                    (*log) << "c \n";
                    opt_conjugate_limit = std::max(opt_conjugate_limit, 
                                                   3*5*sym.group_size().exponent / std::max(1, sym.n_orbits()/2));
                    (*log) << "c optimize generators (opt_passes="
                           << opt_optimize_passes << ", conjugate_limit=" << opt_conjugate_limit << ")" << std::endl;
                    sym.optimize_generators(opt_optimize_passes, opt_addition_limit, 
                                            opt_conjugate_limit, opt_reopt);
                    const double t_optimize_gens = sw.stop();
                    (*log) << "c \t" << "(" << t_optimize_gens << "ms)" << std::endl;
                }
            }

            sw.start();
            (*log) << "c \n";
            (*log) << "c finalize break order and special generators" << std::endl;
            sym.finalize_break_order(formula, sbp);

            if(!struct_only && sym.n_generators() > 0) {
                sw.start();
                (*log) << "c \n";
                (*log) << "c add generic predicates (break_depth=" << break_depth << ")" << std::endl;
                const int constraints = sym.add_lex_leader_for_generators(formula, sbp, break_depth);
                const double t_break_generic = sw.stop();
                (*log) << "c \tadded predicates for " << constraints << " generators (" 
                                                      << t_break_generic << "ms)" << std::endl;
            }

            // deferred writing for proof logging
            sbp.write_all_deferred(order_limit);

            (*log) << "c \n";
            (*log) << "c generation finished" << std::endl;
            (*log) << "c \t[sbp: #constraints " << sbp.n_clauses() << " #add_vars " 
                                                << sbp.n_extra_variables() << "]" << std::endl;

        }

    public:
        void set_struct_only(bool use_only_struct) {
            struct_only = use_only_struct;
        }

        void set_output_graph_file(std::string graph_file) {
            output_graph_filename = graph_file;
        }

        void set_input_graph(dejavu::sgraph* graph) {
            input_graph = graph;
        }

        void set_input_coloring(dejavu::coloring* colors) {
            input_coloring = colors;
        }

        void set_optimize_generators(bool use_optimize_generators) {
            optimize_generators = use_optimize_generators;
        }

        void output_file(std::string& outfile) {
            output_filename = outfile;
            entered_output_file = true;
        }

        long get_order_limit() const {
            return order_limit;
        }

        void set_order_limit(long orderLimit) {
            order_limit = orderLimit;
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

        void set_proof_dense_crossover(int crossover) {
            proof_dense_crossover = crossover;
        }

        void set_proof_sparse_pol(bool pollog) {
            proof_pol_log = pollog;
        }

        void set_dense_model_budget(uint64_t budget) {
            dense_model_budget = budget;
        }

        void set_order_model_budget(uint64_t budget) {
            order_model_budget = budget;
        }

        void set_sparse_model_budget(uint64_t budget) {
            sparse_model_budget = budget;
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

        void set_dejavu_backtrack_limit(int limit = -1) {
            dejavu_backtrack_limit = limit;
        }

        void set_component_size_limit(int limit = -1) {
            graph_component_size_limit = limit;
        }

        void set_full_skip_limit(long limit = -1) {
            full_skip_limit = limit;
        }

        void set_absolute_support_limit(int limit = -1) {
            absolute_support_limit = limit;
        }

        void set_split_limit(int limit = -1) {
            split_limit = limit;
        }

        void set_dejavu_prefer_dfs(bool prefer_dfs) {
            dejavu_prefer_dfs = prefer_dfs;
        }

        void set_preprocess_cnf_subsume(bool preprocessCNFsubsume) {
            preprocess_cnf_subsume = preprocessCNFsubsume;
        }


        void set_preprocess_cnf(bool preprocessCNF) {
            set_preprocess_cnf_pure(preprocessCNF);
            set_preprocess_cnf_unit(preprocessCNF);
        }

        void set_preprocess_cnf_unit(bool preprocessCNF) {
            preprocess_cnf_unit = preprocessCNF;
        }

        void set_preprocess_cnf_eq(bool preprocessCNF) {
            preprocess_cnf_eq = preprocessCNF;
        }

        void set_preprocess_cnf_pure(bool preprocessCNF) {
            preprocess_cnf_pure = preprocessCNF;
        }

        void set_hypergraph_macros(bool hypergraphMacros) {
            hypergraph_macros = hypergraphMacros;
        }

        void set_binary_clauses(bool binaryClauses) {
            binary_clauses = binaryClauses;
        }

        void set_orbitopal_fixing(bool orbitopalFixing) {
            orbitopal_fixing = orbitopalFixing;
        }

        void set_iterate(bool it) {
            iterate = it;
        }

        void set_reorder(bool re) {
            reorder = re;
        }

        void set_order_first(bool re) {
            order_first_lit = re;
        }

        void set_reorder_cliquer(bool reorderCliquer) {
            reorder_cliquer = reorderCliquer;
        }

        void set_iteration_limit(int iterationLimit) {
            iteration_limit = iterationLimit;
        }

        void set_schreier_fixing(bool schreierfixing) {
            schreier_fixing = schreierfixing;
        }

        void set_negation_fixing(bool negationfixing) {
            negation_fixing = negationfixing;
        }

        void set_orbitopal_fixing_only(bool orbitopalFixingOnly) {
            orbitopal_fixing_only = orbitopalFixingOnly;
        }

        void set_proof(proof* my_proof = nullptr) {
            this->my_proof = my_proof;
        }

        void set_add_reduced_as_unit(bool add) {
            add_reduced_variables_as_unit = add;
        }

        void set_tracker(tracker* my_tracker = nullptr) {
            this->track = my_tracker;
        }

        void set_log_output(std::ostream* new_logout) {
            if(new_logout == nullptr) terminate_with_error("log output can not be nullptr");
            log = new_logout;
        }

        void transfer_formula(cnf& formula_db, cnf2wl& formula) {
            std::vector<int> clause;
            for(int i = 0; i < formula_db.n_clauses(); ++i) {
                for(int j = 0; j < formula_db.clause_size(i); ++j) {
                    clause.push_back(formula_db.literal_at_clause_pos(i, j));
                }
                formula.add_clause(clause);
                clause.clear();
            }
        }

        long output_formula(cnf2wl& formula) {
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
            fprintf(output_file, "p cnf %d %d\n",formula.n_variables(), formula.n_clauses());

            // write clauses
            satsuma_flockfile(output_file);
            formula.dimacs_output_clauses_unlocked(output_file);
            satsuma_funlockfile(output_file);
            const long write_data = ftell(output_file); // how many bytes did we write?
            fclose(output_file);

            return write_data;
        }

        void preprocess(cnf2wl& formula, dejavu::sgraph* graph = nullptr) {
            // (For competition:) if formula too big, don't process the formula
            // About 500MB limit
            if(full_skip_limit >= 0 && formula.n_variables() + formula.n_total_clause_size() > full_skip_limit) {
                //(*log) << "c exceeded limit, est: " << formula.n_variables() + formula.n_total_clause_size() << " / " <<  100000000 << std::endl;
                output_formula(formula);
                return;
            }

            stopwatch sw;

            // iteration and iteration limits
            int  iteration = 0;
            reached_limits = false;
            bool is_unsat  = false;  

            if(track) track->update_metric(INIT_VAR, formula.n_variables());
            if(track) track->update_metric(INIT_CL,  formula.n_clauses());
            if(track) track->update_metric(VAR, formula.n_variables());
            if(track) track->update_metric(CL, formula.n_clauses());

            std::vector<int> proof_fix_literals;

            while(true) {
                if(my_proof) my_proof->set_proof_dense_crossover(proof_dense_crossover);
                if(my_proof) my_proof->set_pol_logging(proof_pol_log);
                if(my_proof) my_proof->header(formula.n_clauses());

                // apply rudimentary, symmetry-preserving CNF preprocessing
                if(preprocess_cnf_unit || preprocess_cnf_pure) {
                    if(track) track->force_print();
                    if(track) track->update_routine(PREPROCESS);
                    // abort if not implemented
                    if(my_proof && preprocess_cnf_eq && add_reduced_variables_as_unit) 
                        terminate_with_error("equivalent literals is incompatible with adding reduced variables as unit literals");

                    (*log) << "c\n";
                    (*log) << "c simplify cnf" << std::endl;
                    sw.start();

                    // statistics
                    int unit_propagations = 0;
                    int pure_literal_num = 0;
                    int subsumed = 0;

                    // propagate unit literals
                    if(preprocess_cnf_unit)
                        unit_propagations = formula.propagate();

                    // pure literals
                    if(preprocess_cnf_pure) {
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
                        pure_literal_num = pure_literals.size();
                        for(const auto lit : pure_literals) {
                            formula.assign_literal(lit);
                        }
                    }

                    // propagate unit again if pure was applied
                    if(preprocess_cnf_pure && preprocess_cnf_unit) {
                        unit_propagations += formula.propagate();
                    }

                    // subsumption
                    if(preprocess_cnf_subsume) subsumed = formula.mark_subsumed_clauses();
                    const double t_unit = sw.stop();
                    (*log) << "c\t -units=" << unit_propagations << 
                        ", -pures=" << pure_literal_num << 
                        ", -subsumed=" << subsumed << " (" << t_unit << "ms)" << std::endl;
                    if(track) track->add_to_metric(PROPAGATIONS, unit_propagations);
                }

                if(formula.is_conflicting()) {
                    reached_limits = true;
                    is_unsat       = true;
                    (*log) << "c " << std::endl;
                    if(track) track->print_unsat();
                    formula.reset_assignment();
                    formula.clear();
                    formula.reserve(1, 1);
                    std::vector<int> empty_clause;
                    formula.add_clause(empty_clause);
                    if(my_proof) my_proof->drat_clause({});
                }

                // keep track of literals that will be reduced away 
                if(add_reduced_variables_as_unit) {
                    for(int i = 0; i < 2*formula.n_variables(); ++i) {
                        const int l = graph_to_sat(i);
                        if(formula.assigned(l) == 1) {
                            proof_fix_literals.push_back(l);
                        }
                    }
                }

                if(track) track->update_metric(VAR, formula.n_variables());
                if(track) track->update_metric(CL, formula.n_clauses());

                // transfer watched literal CNF into a reduced, duplicate-free CNF representation
                if(track) track->update_routine(DEDUPLICATE);
                constexpr bool keep_original_order = true;
                (*log) << "c\n";
                (*log) << "c make clause database (keep_order=" << keep_original_order << ")"  << std::endl;
                //computational_cost += 10*formula.n_total_clause_size() + formula.n_variables();
                track->add_to_metric(COST_SYM, 10*formula.n_total_clause_size() + formula.n_variables());
                //sw.start();
                if(preprocess_cnf_eq) formula.equivalent_literals();
                cnf formula_db;
                formula_db.read_from_cnf2wl(formula, keep_original_order, my_proof);
                (*log) << "c \t ulc=" << formula_db.ulc_add_amo(my_proof) << ", bin=" << formula_db.compute_binary() << std::endl;
                (*log) << "c \t -dupl_cl=" << formula_db.n_duplicate_clauses_removed()
                       << ", +amo_cl=" << formula_db.n_amo_clauses_added() 
                       << ", <>eq_subst=" << formula_db.n_eq_literal_subst();
                formula.clear();
                if(track) track->add_to_metric(AMO_BINARY, formula_db.n_amo_clauses_added());
                (*log) << std::endl;

                if(track) track->update_metric(VAR, formula_db.n_variables());
                if(track) track->update_metric(CL, formula_db.n_clauses());
                //formula_db.equivalent_literals();

                predicate sbp(formula_db.n_variables(), track, my_proof);
                if(!formula.is_conflicting()) {
                    // generate symmetry breaking predicates
                    sbp.formula = &formula_db;
                    sbp.set_dense_model_budget(dense_model_budget);
                    sbp.set_order_model_budget(order_model_budget);
                    sbp.set_sparse_model_budget(sparse_model_budget);
                    sbp.set_orbitopal_fixing(orbitopal_fixing);
                    sbp.set_orbitopal_fixing_only(orbitopal_fixing_only);
                    generate_symmetry_predicate(formula_db, sbp);
                }

                // as formula becomes smaller we increase iteration limit
                const double size           = formula_db.n_len() + formula_db.n_variables();
                // const double size_falloff   = 1 - std::min((size / (1 << 22)), 1.0);
                // const int  iteration_max    = std::max(1, static_cast<int>(std::ceil(iteration_limit * size_falloff)));
                //
                constexpr double S = static_cast<double>(1ULL << 23); 
                constexpr double p = 1.5; 
                const double s     = std::max(size, 1.0);
                const double raw   = std::pow(S / s, p);
                const int iteration_max = 
                    std::clamp(static_cast<int>(std::ceil(raw)), 1, static_cast<int>(iteration_limit));

                if(iterate && orbitopal_fixing_only && iteration < iteration_max && sbp.n_clauses() >= 1 && 
                   formula.n_variables() < 20000 && !reached_limits) {
                    ++iteration;
                    track->update_metric(ITERATIONS, iteration);
                    formula.clear();
                    formula.reserve(formula_db.n_variables() + sbp.n_extra_variables(),
                                    formula_db.n_clauses()   + sbp.n_clauses());
                    transfer_formula(formula_db, formula);
                    (*log) << "c " << std::endl;
                    (*log)<< "c ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n";
                    (*log) << "c " << std::endl;
                    (*log) << "c iterate (" << iteration << "/" << iteration_max << ")" << std::endl;
                    for(int i = 0; i < sbp.n_clauses(); ++i) formula.add_clause(sbp.get_clause(i));
                    continue;
                }


                // write proof for fixed up literals (such as to finish proof before writing output)
                if(is_unsat) proof_fix_literals.clear(); // ...but not if UNSAT
                if(my_proof) { 
                    for(size_t i = 0; i < proof_fix_literals.size(); ++i) {
                        my_proof->drat_clause({proof_fix_literals[i]});
                    }
                }

                (*log) << "c \n";
                (*log) << "c preprocessing finished" << std::endl;

                // output result
                if(track) track->force_print();
                if(track) track->update_routine(OUTPUT);
                (*log) << "c \n";
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
                fprintf(output_file, "p cnf %d %d\n",formula_db.n_variables() + sbp.n_extra_variables(),
                        formula_db.n_clauses()   + sbp.n_clauses() + 
                        static_cast<int>(proof_fix_literals.size()));

                // write clauses
                satsuma_flockfile(output_file);
                formula_db.dimacs_output_clauses_unlocked(output_file);
                sbp.dimacs_output_clauses(output_file);

                // write unit clauses for fixed up proof 
                for(size_t i = 0; i < proof_fix_literals.size(); ++i) {
                    const int l = proof_fix_literals[i];
                    output_integer(output_file, l);
                    satsuma_putc(' ',  output_file);
                    satsuma_putc('0',  output_file);
                    satsuma_putc('\n', output_file);
                }

                satsuma_funlockfile(output_file);
                const long write_data = ftell(output_file); // how many bytes did we write?
                fclose(output_file);

                if(track) track->force_print();
                if(track) track->update_routine(REFINE);
                if(track) track->print_output(write_data, entered_output_file?output_filename:"stdout");
                break;
            }
        }

        void preprocess(pbf& formula, bool knf = false) {
            stopwatch sw;

            if(my_proof) my_proof->set_proof_dense_crossover(proof_dense_crossover);
            if(my_proof) my_proof->set_pol_logging(proof_pol_log);
            if(my_proof) my_proof->header(formula.n_clauses() - formula.is_optimization() + 
                                          formula.n_duplicate_clauses_removed() + formula.n_duplicate_eqs_removed()
                                          + formula.n_eq_constraints());

            std::vector<int> proof_fix_literals;

            // generate symmetry breaking predicates
            predicate sbp(formula.n_variables(), track, my_proof);
            sbp.formula = &formula;
            sbp.set_dense_model_budget(dense_model_budget);
            sbp.set_order_model_budget(order_model_budget);
            sbp.set_sparse_model_budget(sparse_model_budget);
            generate_symmetry_predicate(formula, sbp);

            // output result
            (*log) << "c \n";
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
            if(!knf) fprintf(output_file, "* #variable= %d #constraint= %d #equal= %d",
                                                 formula.n_variables() + sbp.n_extra_variables(),
                                                 formula.n_clauses() - formula.is_optimization() + sbp.n_clauses() + 
                                                 static_cast<int>(proof_fix_literals.size()) ,
                                                 formula.n_eq_constraints());
            if(!knf && formula.n_intsize() >= 0) fprintf(output_file, " intsize= %d", formula.n_intsize());

            if(knf) fprintf(output_file, "p knf %d %d",
                                                 formula.n_variables() + sbp.n_extra_variables(),
                                                 formula.n_clauses() + sbp.n_clauses());

            // write clauses
            satsuma_flockfile(output_file);
            satsuma_putc('\n', output_file);
            if(!knf) formula.dimacs_output_pb_constraints_unlocked(output_file);
            else     formula.dimacs_output_knf_unlocked(output_file);

            if(!knf) sbp.pb_output_clauses(output_file);
            else     sbp.dimacs_output_clauses(output_file);

            satsuma_funlockfile(output_file);
            const long write_data = ftell(output_file); // how many bytes did we write?
            fclose(output_file);
            (*log) << "c \twrote " << 1.0*write_data / 1000000.0 << "MB" << std::endl;
        }
    };
}

#endif //SATSUMA_SATSUMA_H
