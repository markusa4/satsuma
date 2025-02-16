// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_CNF2WL_H
#define SATSUMA_CNF2WL_H

#include <string>
#include "utility.h"
#include "dejavu/ds.h"
#include <charconv>
#include <bitset> 

class cnf2wl {
    std::vector<std::pair<int, int>> clauses_pt;
    std::vector<std::pair<int, int>> clauses_watches;
    std::vector<int> clauses;
    std::vector<std::vector<int>>    literal_used_list;
    std::vector<std::vector<int>>    variable_watches_clause;

    std::vector<int> assignment;

    int number_of_variables = 0;
    int units_applied = 0;
    int redundant_removed = 0;
    int subsumptions_found = 0;
    dejavu::ds::markset in_units;
    std::vector<int>    units;

    dejavu::ds::markset clause_satisfied;
    dejavu::ds::markset found_literal;
    dejavu::ds::markset test_redundant;
    dejavu::ds::markset test_for_subsumption;

public:
    void reserve(int n, int m) {
        number_of_variables = n;
        clauses_pt.reserve(m);
        clauses.reserve(4*m);
        clauses_watches.resize(m);
        literal_used_list.resize(2*n);
        variable_watches_clause.resize(2*n);
        assignment.resize(2*n);
        found_literal.initialize(2*n);
        test_redundant.initialize(2*n);
        test_for_subsumption.initialize(m);

        clause_satisfied.initialize(m);
        in_units.initialize(2*n);
    }

    void mark_literal_uses() {
        for(int i = 0; i < n_clauses(); ++i) {
            if(clause_satisfied.get(i)) continue;
            for(int j = 0; j < clause_size(i); ++j) {
                const int lit = literal_at_clause_pos(i, j);
                if(assigned(lit) == 0) found_literal.set(sat_to_graph(lit));
            }
        }
    }

    #define HASH0(x) (abs((x*417) % 63 + x>0?1:0))

    unsigned long clause_signature(int cl) {
        unsigned long sig = 0;
        for(int i = 0; i < clause_size(cl); ++i) {
            const int lit = literal_at_clause_pos(cl, i);
            if(assigned(lit) != 0) continue;
            const int mv  = HASH0(lit);
            unsigned long sigmv = 1 << mv;
            sig = sig | sigmv;
        }
        return sig;
    }


    int mark_subsumed_clauses() {
        constexpr int subsume_size_limit_small = 16;
        constexpr int subsume_size_limit_big   = 1024;
        constexpr int max_used_list_size = 64;

        std::vector<unsigned long> signatures;
        signatures.reserve(n_clauses());

        for(int i = 0; i < n_clauses(); ++i) {
            signatures.push_back(clause_signature(i));
        }

        std::vector<int> test_clauses;

        for(int i = 0; i < n_clauses(); ++i) {
            test_redundant.reset();
            if(clause_satisfied.get(i)) continue;
            if(clause_size(i) > subsume_size_limit_small) continue;
            test_for_subsumption.reset();
            test_clauses.clear();

            int clause_compare_size = 0;

            for (int j = 0; j < clause_size(i); ++j) {
                const int lit = sat_to_graph(literal_at_clause_pos(i, j));
                if(assigned(graph_to_sat(lit)) != 0) continue;
                ++clause_compare_size;
                test_redundant.set(lit);
                if(literal_used_list[lit].size() > max_used_list_size) continue;
                for(int used = 0; used < static_cast<int>(literal_used_list[lit].size()); ++used) {
                    const int cl = literal_used_list[lit][used];
                    if(clause_size(cl) > subsume_size_limit_big) continue;
                    if(!test_for_subsumption.get(cl)) {
                        test_for_subsumption.set(cl);
                        test_clauses.push_back(cl);
                    }
                }
            }

            for(const auto i2 : test_clauses) {
                if(i == i2) continue;
                if(clause_size(i2) <= clause_size(i)) continue;
                if(clause_satisfied.get(i)) continue;
                //if(clause_size(i2) > subsume_size_limit) continue;
                
                // hash trick
                const std::bitset<64> sig_diff = (signatures[i] & (~signatures[i2]));
                if(sig_diff.count() != 0) continue;

                // actual test
                int  literals_found = 0;
                for (int j = 0; j < clause_size(i2); ++j) {
                    if(assigned(literal_at_clause_pos(i2, j)) != 0) continue;
                    if(test_redundant.get(sat_to_graph(literal_at_clause_pos(i2, j)))) {
                        ++literals_found;
                    }
                }

                // check if success
                if(literals_found == clause_size(i)) {
                    ++subsumptions_found;
                    //std::clog << "subsume " << subsumptions_found << " (" << i << "/" << n_clauses() << ")" << std::endl;
                    clause_satisfied.set(i2);
                }
            }
        }
        return subsumptions_found;
    }

    bool is_literal_marked_used(int lit) {
        return found_literal.get(sat_to_graph(lit));
    }

    int satisfied_clauses() {
        int satisfied = 0;
        for(int i = 0; i < n_clauses(); ++i) {
            satisfied += clause_satisfied.get(i);
        }
        return satisfied;
    }

    bool is_satisfied(int clause) {
        return clause_satisfied.get(clause);
    }

    void add_clause(std::vector<int>& clause) {
        test_redundant.reset();
        for(auto& l : clause) {
            const int graph_l  = sat_to_graph(l);
            const int graph_nl = sat_to_graph(-l);
            if(test_redundant.get(graph_l)) continue;
            if(test_redundant.get(graph_nl)) {
                ++redundant_removed;
                return;
            }
            test_redundant.set(graph_l);
        }

        const int clause_number = clauses_pt.size();
        clauses_pt.emplace_back(clauses.size(), clauses.size() + clause.size());
        clauses.insert(clauses.end(), clause.begin(), clause.end());
        for(auto& l : clause) {
            assert(l != 0);
            [[maybe_unused]] const int v = abs(l) - 1;
            assert(v >= 0);
            assert(v < number_of_variables);
            literal_used_list[sat_to_graph(l)].push_back(clause_number);
        }

        initialize_watches(clause_number);
    }

    int propagate () {
        int propagations = 0;
        while(true) {
            const int next_unit_literal = dequeue_next_unit();
            if(next_unit_literal == 0) break;
            //std::clog << "unit " << next_unit_literal << std::endl;
            assign_literal(next_unit_literal);
            ++propagations;
        }
        return propagations;
    }

    void queue_units(int literal, int reason_clause) {
        if(!in_units.get(sat_to_graph(literal))) {
            in_units.set(sat_to_graph(literal));
            units.push_back(literal);
        }
    }

    int dequeue_next_unit() {
        if(units.empty()) return 0;
        const int c = units.back();
        units.resize(units.size()-1);
        in_units.unset(sat_to_graph(c));
        return c;
    }


    void assign_literal(int literal) {
        assert(assignment[sat_to_graph(literal)] == 0);
        assert(assignment[sat_to_graph(-literal)] == 0);
        assignment[sat_to_graph(literal)]  = 1;
        assignment[sat_to_graph(-literal)] = -1;

        for(auto c : literal_used_list[sat_to_graph(literal)]) update_satisfied(c);
        while(!variable_watches_clause[abs(literal)].empty()) {
            int next_watched_clause = variable_watches_clause[abs(literal)].back();
            int pos = variable_watches_clause[abs(literal)].size() - 1;
            update_watches(next_watched_clause, abs(literal), pos);
        }
    }

    int assigned(int literal) {
        return assignment[sat_to_graph(literal)];
    }


    void update_satisfied(int clause_number) {
        clause_satisfied.set(clause_number);
    }

    void add_watch(int variable, int watch_clause) {
        variable_watches_clause[abs(variable)].push_back(watch_clause);
    }

    void remove_watch(int variable, int watch_pos) {
        //std::clog << "remove_watch: " << variable << "<-" << watch_pos << std::endl;
        int back_watch = variable_watches_clause[variable].back();
        variable_watches_clause[variable][watch_pos] = back_watch;
        variable_watches_clause[variable].resize(variable_watches_clause[variable].size()-1);
    }

    void initialize_watches(int clause_number) {
        if(clause_size(clause_number) == 1) {
            queue_units(literal_at_clause_pos(clause_number, 0), clause_number);
        } else {
            add_watch(literal_at_clause_pos(clause_number, 0), clause_number);
            add_watch(literal_at_clause_pos(clause_number, 1), clause_number);
            clauses_watches[clause_number] = {clauses_pt[clause_number].first, clauses_pt[clause_number].first+1};
            assert(clauses[clauses_watches[clause_number].first]  == literal_at_clause_pos(clause_number, 0));
            assert(clauses[clauses_watches[clause_number].second] == literal_at_clause_pos(clause_number, 1));
        }
    }

    void update_watches(int clause_number, int from_variable, int from_pos) {
        if(clause_satisfied.get(clause_number)) {
            remove_watch(from_variable, from_pos);
            return;
        }
        auto [watch1, watch2] = clauses_watches[clause_number];
        //std::clog << clause_number << ":" << abs(clauses[watch1]) << ", " <<  abs(clauses[watch2]) << ", " << from_variable << std::endl;
        assert(abs(clauses[watch1]) == from_variable || abs(clauses[watch2]) == from_variable);
        int new_watch = -1;
        for(int i = clauses_pt[clause_number].first; i < clauses_pt[clause_number].second; ++i) {
            if(i != watch1 && i != watch2 && assigned(clauses[i]) == 0) {
                new_watch = i;
                break;
            }
        }
        if(new_watch == -1) {
            remove_watch(from_variable, from_pos);
            if (abs(clauses[watch1]) == from_variable) {
                queue_units(clauses[watch2], clause_number);
            } else {
                assert(abs(clauses[watch2]) == from_variable);
                queue_units(clauses[watch1], clause_number);
            }
        } else {
            remove_watch(from_variable, from_pos);
            add_watch(clauses[new_watch], clause_number);
            if (abs(clauses[watch1]) == from_variable) {
                clauses_watches[clause_number].first = new_watch;
            } else {
                assert(abs(clauses[watch2]) == from_variable);
                clauses_watches[clause_number].second = new_watch;
            }
        }
    }

    int clause_size(int c) {
        return clauses_pt[c].second - clauses_pt[c].first;
    }

    int literal_at_clause_pos(int c, int i) {
        return clauses[clauses_pt[c].first + i];
    }

    int n_total_clause_size() {
        return clauses.size();
    }

    int n_len() {
        return clauses.size();
    }

    int n_clauses() {
        return clauses_pt.size();
    }

    int n_redundant_clauses() {
        return redundant_removed;
    }

    int n_variables() {
        return number_of_variables;
    }

    void dimacs_output_clauses(std::ostream& out) {
        for(int i = 0; i < n_clauses(); ++i) {
            for (int j = 0; j < clause_size(i); ++j) {
                int l = literal_at_clause_pos(i, j);
                out << l << " ";
            }
            out << "0" << "\n";
        }
    }

    void dimacs_output_clauses(FILE* out) {
        constexpr int buffer_size = 16;
        char          buffer[buffer_size];

        for(int i = 0; i < n_clauses(); ++i) {
            for (int j = 0; j < clause_size(i); ++j) {
                const int l = literal_at_clause_pos(i, j);
                std::to_chars(buffer, buffer + buffer_size, l);
                for(int j = 0; buffer[j] != 0; ++j) satsuma_putc(buffer[j], out);
                satsuma_putc(' ', out);
            }
            satsuma_putc('0', out);
            satsuma_putc('\n', out);
        }
    }

    void clear() {
        clauses_pt.clear();
        clauses_watches.clear();
        clauses.clear();
        literal_used_list.clear();
        variable_watches_clause.clear();
        assignment.clear();
        units.clear();

        clauses_pt.shrink_to_fit();
        clauses_watches.shrink_to_fit();
        clauses.shrink_to_fit();
        literal_used_list.shrink_to_fit();
        variable_watches_clause.shrink_to_fit();
        assignment.shrink_to_fit();
        units.shrink_to_fit();

        number_of_variables = 0;
        units_applied = 0;
        redundant_removed = 0;
        in_units.initialize(0);

        clause_satisfied.initialize(0);
        found_literal.initialize(0);
        test_redundant.initialize(0);

    }
};

#endif //SATSUMA_CNF2WL_H
