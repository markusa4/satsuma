// Copyright 2026 Markus Anders
// This file is part of satsuma 1.4.
// See LICENSE for extended copyright information.


#include <cstdint>
#include <chrono>
#include <algorithm>
#include <vector>
#include <iomanip>
#include <iostream>
#include "utility.h"

#ifndef SATSUMA_TRACKER_H
#define SATSUMA_TRACKER_H

namespace satsuma {
    #define console_bold "\033[1m"
    #define console_green "\033[32m"
    #define console_blue "\033[36m"
    #define console_orange "\033[33m"
    #define console_bright_blue "\033[96m"
    #define console_magenta "\033[35m"
    #define console_red "\033[33m"
    #define console_neutral "\033[0m"

    static void console_split() {
        std::clog << console_blue << "c ------------------------------------------------------------------\n" << console_neutral;
    }

    /**
     * Used to make the output look a bit more structured.
     */
    static void progress_print_split() {
        console_split();
        std::clog << console_blue << "c " <<console_neutral << "[time] it op vars clauses  gens structs  " 
                  << console_orange << "fix cut lex  " << console_magenta "remain%\n" << console_neutral;
        console_split();
    }

    /**
     * Prints heading of table in the output.
     */
    static void progress_print_header() {
        progress_print_split();
        PRINT(std::setw(11) << std::left <<"T (ms)" << std::setw(11) << "delta(ms)" << std::setw(12) << "proc"
              << std::setw(16) << "p1"        << std::setw(16)        << "p2");
        progress_print_split();
    }

    enum tracker_metrics {COST_SYM, COST_SCHREIER, COST_OTHER, 
                          INIT_VAR, INIT_CL, VAR, CL, 
                          SYM_UNIT, SYM_BINARY, SYM_LEX, SYM_LEX_SUPPORT,
                          SYM_GENS, JOHNSON, ROW, ROW_COLUMN,
                          ITERATIONS, PROPAGATIONS, SCHREIER_LEVELS, 
                          GEN_SUPPORT, ORBITOPAL_FIX, AMO_BINARY};

    /**
     * \brief Prints information to the console.
     *
     * Contains additional facilities to measure elapsed time in-between prints.
     */
    class tracker {
        std::chrono::high_resolution_clock::time_point first;
        std::chrono::high_resolution_clock::time_point previous;

        std::vector<uint64_t> metrics {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        uint64_t last_print_at_cost = 0;

        const int interval_max = 16;
        int interval           = 0;
        int verbosity          = 0;
        const uint64_t print_interval  = 150000000;
        profiler_token current_routine = PARSE;

        int    last_update_n = 0;
        int    last_update_m = 0;
        double last_col   = 0;
        int    last_leaf_counter = 0;

        std::vector<std::pair<std::string, double>> results;
        std::vector<double> time_by_token {0,0,0,0,0,0,0,0,0,0,0,0,0};
        std::vector<std::string> token_to_name = {
            "dejavu", 
            "structure", 
            "simplify", 
            "parse", 
            "hypergraph", 
            "refine", 
            "schreier", 
            "optimize", 
            "order", 
            "break", 
            "deduplicate", 
            "output", 
            "other"};
    public:

        bool h_silent = false;

        tracker(int verbosity = 0) : verbosity(verbosity) {
            first     = std::chrono::high_resolution_clock::now();
            previous  = first;
        }

        inline uint64_t cost_estimate() {
            return metrics[COST_SCHREIER] + metrics[COST_SYM] + metrics[COST_OTHER];
        }

        void add_time(profiler_token token, double result) {
            time_by_token[token] += result;
        }

        void force_print() {
            print_status();
        }

        double estimate_progress() {
            return 0;
        }

        void maybe_print() {
            if(cost_estimate() - last_print_at_cost > print_interval) {
                print_status();
            }
        }
        void print_table_explain() {
            if(h_silent) return;
            progress_print_split();
        }

        void print_status() {
            if(h_silent) return;
            --interval;
            if(interval <= 0) {
                print_table_explain();
                interval = interval_max;
            }
            std::clog << "c ";
            auto now = std::chrono::high_resolution_clock::now();
            std::clog << "[" << std::setprecision(2) << std::fixed
                      << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - first).count()) / 1000000000.0 
                      << "]";
            last_print_at_cost = cost_estimate();
            std::clog << " ";
            std::clog << metrics[ITERATIONS];
            std::clog << " ";
            switch(current_routine) {
                case PARSE:
                std::clog << "parse   ";
                break;
                case PREPROCESS:
                std::clog << "simplify";
                break;
                case REFINE:
                std::clog << "refine  ";
                break;
                case OUTPUT:
                std::clog << "output  ";
                break;
                case OPTIMIZE:
                std::clog << "optimize";
                break;
                case BREAK:
                std::clog << "break   ";
                break;
                case DETECT_GENERIC:
                std::clog << "dejavu  ";
                break;
                case DETECT_SPECIAL:
                std::clog << "structs ";
                break;
                case SCHREIER:
                std::clog << "schreier";
                break;
                case ORDER:
                std::clog << "lexorder";
                break;
                case HYPERGRAPH:
                std::clog << "shrink  ";
                break;
                case DEDUPLICATE:
                std::clog << "dedupl  ";
                break;
                default:
                std::clog << "unknown";
                break;
            }
            std::clog << " ";
            std::clog << metrics[VAR];
            std::clog << " ";
            std::clog << metrics[CL];
            std::clog << " ";
            std::clog << " ";
            std::clog << metrics[SYM_GENS];
            std::clog << " ";
            std::clog << metrics[ROW] +  metrics[ROW_COLUMN] +  metrics[JOHNSON];
            std::clog << " ";
            std::clog << " ";
            std::clog << console_orange << metrics[SYM_UNIT];
            std::clog << " ";
            std::clog << console_orange << metrics[SYM_BINARY];
            std::clog << " ";
            std::clog << console_orange << metrics[SYM_LEX];
            std::clog << " ";
            std::clog << " ";
            double prog = 1.0;
            if(metrics[CL] != 0) prog = 1.0*metrics[CL] / metrics[INIT_CL];
            std::clog << console_magenta << prog * 100 << "%" << console_neutral;
            std::clog << std::endl;
            
        }

        void add_to_metric(tracker_metrics metric, uint64_t value) {
            metrics[metric] += value;
            maybe_print();
        }

        void update_metric(tracker_metrics metric, uint64_t value) {
            metrics[metric] = value;
            maybe_print();
        }

        void update_routine(profiler_token new_routine) {
            maybe_print();
            auto now = std::chrono::high_resolution_clock::now();
            add_time(current_routine, 
                    (std::chrono::duration_cast<std::chrono::nanoseconds>(now - previous).count()) / 1000000.0);
            current_routine = new_routine;
            previous  = now;
        }

        void print_header() const {
            return;
            if(h_silent) return;
            progress_print_header();
        }

        void print_unsat() const {
            if(h_silent) return;
            console_split();
            std::clog << "c " << "\n";
            std::clog << console_bold << "c UNSATISFIABLE" << console_neutral << std::endl;
            std::clog << "c " << "\n";
            console_split();
        }

        void print_output(uint64_t bytes, std::string&& filename) const {
            if(h_silent) return;
            console_split();
            std::clog << "c wrote " << bytes / 1000000.0 << "MB to " << filename << std::endl;
        }

        void print_split() const {
            if(h_silent) return;
            progress_print_split();
        }


        void status(const std::string& state) const {
            if(h_silent) return;
            PRINT("\r" << state);
        }

        void print(const std::string& str, int verb=0) const {
            if(verb > verbosity || h_silent) return;
            std::clog << "c "  << token_to_name[current_routine] << "::" << str << "\n";
        }

        void print_stats() {
            if(h_silent) return;
            //std::clog << "c " << "Detected symmetry:" << "\nc \n";
            std::clog << "c "  << std::left << std::setw(20) << "dejavu_gens" << "= " << std::left << std::setw(12) << metrics[SYM_GENS] 
                      << "\t(average_support = " << (1.0*metrics[GEN_SUPPORT] / std::max((uint64_t)1, metrics[SYM_GENS])) << ")\n";
            std::clog << "c "  << std::left << std::setw(20) << "row" << "= "<< std::left << std::setw(12) << metrics[ROW] << "\n";
            std::clog << "c "  << std::left << std::setw(20) << "row_column" << "= "<< std::left << std::setw(12) << metrics[ROW_COLUMN] << "\n";
            std::clog << "c "  << std::left << std::setw(20) << "johnson" << "= "<< std::left << std::setw(12) << metrics[JOHNSON] << "\n";
            std::clog << "c \n";
            // std::clog << "c \nc " << "Constraints added by symmetry:" << "\nc \n";
            std::clog << "c "  << std::left << std::setw(20) << "symmetry_units" << "= "<< std::left << std::setw(12) << metrics[SYM_UNIT]
                      << "\t(orbitopal_units = " << metrics[ORBITOPAL_FIX] << ")\n";
            std::clog << "c "  << std::left << std::setw(20) << "symmetry_binary" << "= "<< std::left<< std::setw(12) << metrics[SYM_BINARY]
                      << "\t(amo_binary = " << metrics[AMO_BINARY] << ")\n";
            std::clog << "c "  << std::left << std::setw(20) << "symmetry_lex" << "= "<< std::left<< std::setw(12) << metrics[SYM_LEX]
                      << "\t(average_depth = " << (1.0*metrics[SYM_LEX_SUPPORT] / std::max((uint64_t)1, metrics[SYM_LEX])) << ")\n";
            std::clog << "c \n";
            //std::clog << "c \nc " << "Algorithm statistics:" << "\nc \n";
            std::clog << "c "  << std::left << std::setw(20) << "iterations" << "= "<< std::left << std::setw(12) << metrics[ITERATIONS] << "\n";
            std::clog << "c "  << std::left << std::setw(20) << "propagations" << "= "<< std::left<< std::setw(12) << metrics[PROPAGATIONS] << "\n";
            std::clog << "c "  << std::left << std::setw(20) << "schreier_levels" << "= "<< std::left<< std::setw(12) << metrics[SCHREIER_LEVELS] << "\n";
        }

        void print_profile(const double independent_total = -1) {
            if(h_silent) return;
            update_routine(current_routine);
            double total = 0;
            for (auto const & time: time_by_token) {
                total += time;
            }

            // if(independent_total > 0 && independent_total > total) {
            // const double t_other = independent_total - total;
            //    add_result(OTHER, t_other);
            //    total = independent_total;
            //}

            // construct "results" form result_by_token and token_to_name
            for(size_t i = 0; i < time_by_token.size(); ++i) 
                results.emplace_back(token_to_name[i], time_by_token[i]);

            if(total == 0) total += 0.001;

            std::sort(results.begin(), results.end(), [](auto &left, auto &right) {
                    return left.second > right.second;
                    });

            std::clog << std::setprecision(2) << std::fixed;
            for(auto const& [name, time] : results) {
                if(time < 0.005) break;
                std::clog << "c " << std::right << std::setw(22) << time << "ms" << std::right << std::setw(6) 
                          << (time/total)*100 << std::setw(1) << "%"  << std::left << " " << name <<  "\n";
            }
            std::clog << "c         ───────────────────────────────────────────────\n";
            std::clog << "c " << std::right << std::setw(22) << total << "ms" << std::right << std::setw(6) << 100 << std::setw(1) << "%"  << std::left << " " << "total" <<  "\n";
        }
    };
}

#endif //DEJAVU_TRACKER_H
