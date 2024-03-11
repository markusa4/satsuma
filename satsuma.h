// Copyright 2024 Markus Anders
// This file is part of satsuma 1.0.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_SATSUMA_H
#define SATSUMA_SATSUMA_H

#define SATSUMA_VERSION_MAJOR 1
#define SATSUMA_VERSION_MINOR 0

#include <utility>
#include "dejavu/dejavu.h"
#include "cnf.h"
#include "utility.h"
#include "group_analyzer.h"

namespace satsuma {
    /**
     * \brief The satsuma preprocessor.
     *
     */
    class preprocessor {

        bool entered_output_file = false;
        std::string output_filename = "";
        bool struct_only = false;
    
        /**
            Compute a symmetry breaking predicate for the given formula.

            @param formula The given CNF formula.
        */
        void generate_symmetry_predicate(cnf& formula) {
            stopwatch sw;
            stopwatch total;

            total.start();
            // transform the formula into a graph and apply color refinement to approximate orbits
            std::clog << "c approximating orbits";
            sw.start();
            group_analyzer symmetries;
            symmetries.compute_from_cnf(formula);
            std::clog << "\t(" << sw.stop() << "ms)" << std::endl;

            std::clog << "c\t #orbits " << symmetries.n_orbits() << std::endl;

            // now try to detect and break specific group actions
            std::clog << "c detecting group actions" << std::endl;
            sw.start();

            predicate sbp(formula.n_variables());

            // symmetries.detect_symmetric_action(formula, sbp);
            symmetries.detect_johnson_arity2(formula,sbp);
            symmetries.detect_row_column_symmetry(formula, sbp);
            symmetries.detect_row_symmetry(formula, sbp);

            std::clog << "c\t (" << sw.stop() << "ms)" << std::endl;

            // next, apply dejavu on remainder, and break generators with generic strategy
            std::clog << "c detecting symmetries on remainder " << std::endl;
            sw.start();
            symmetries.detect_symmetries_generic();
            std::clog << "\t(" << sw.stop() << "ms)" << std::endl;
            std::clog << "c\t #symmetries " << symmetries.group_size() << " #generators " << symmetries.n_generators()
                       << std::endl;

            sw.start();
            if(!struct_only) {
                std::clog << "c adding binary clauses" << std::endl;
                const int binary_clauses = symmetries.add_binary_clauses_no_schreier(formula, sbp);
                if (binary_clauses > 0) std::clog << "c\t produced " << binary_clauses << " clauses" << std::endl;
                std::clog << "c adding generic predicates" << std::endl;
                symmetries.add_lex_leader_for_generators(sbp);
                std::clog << "c \t(" << sw.stop() << "ms)" << std::endl;
            }

            std::clog << "c total generation time " << total.stop() << "ms" << std::endl;
            std::clog << "c\t [sbp: #clauses " << sbp.n_clauses() << " #add_vars " <<
                                sbp.n_extra_variables() << "]"<< std::endl;

            // output result
            std::clog << "c writing result" << std::endl;

            std::ofstream output_file_stream;
            if(entered_output_file) output_file_stream.open(output_filename);
            std::ostream& test_output = entered_output_file? output_file_stream : std::cout;

            test_output << "p cnf " << formula.n_variables() + sbp.n_extra_variables() << " " <<
                                     formula.n_clauses() + sbp.n_clauses() << "\n";

            formula.dimacs_output_clauses(test_output);
            sbp.dimacs_output_clauses(test_output);
        }

    public:
        void set_struct_only(bool use_only_struct) {
            struct_only = use_only_struct;
        }

        void output_file(std::string& outfile) {
            output_filename = outfile;
            entered_output_file = true;
        }

        void preprocess(cnf& formula) {
            generate_symmetry_predicate(formula);
        }
    };
}

#endif //SATSUMA_SATSUMA_H
