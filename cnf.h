// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_CNF_H
#define SATSUMA_CNF_H

#include <string>
#include "dejavu/groups.h"
#include "tsl/robin_set.h"
#include "utility.h"
#include "cnf2wl.h"

/**
 * A CNF formula with a hash table of clauses. Can not contain duplicate clauses.
 */
class cnf {
    // hash sets for clauses
    tsl::robin_set<std::vector<int>, any_hash>                  clause_db_arbitrary;
    tsl::robin_set<std::pair<int, int>, pair_hash>                  clause_db_size2;
    tsl::robin_set<std::tuple<int, int, int>, triple_hash>          clause_db_size3;

    // clauses as a vector
    std::vector<std::pair<int, int>> clauses_pt;
    std::vector<int> clauses;

    // used lists
    std::vector<std::pair<int, int>> variable_to_nclauses;
    std::vector<std::vector<int>>    variable_used_list;

    // statistics
    int number_of_variables       = 0;
    int removed_duplicate_clauses = 0;

    // auxiliary data structures used for methods
    dejavu::ds::markset test_used;
    dejavu::ds::markset support_test;
    std::vector<int> need_to_test_clauses;
    std::vector<int> test_clause;
    std::vector<std::pair<int, int>> add_pairs;

    bool keep_original_order = true;

public:
    /**
     * Initializes the data structure using a `cnf2wl` formula.
     *
     * @param other_formula the other formula
     */
    void read_from_cnf2wl(cnf2wl& other_formula, bool original_order = true) {
        keep_original_order = original_order;
        reserve(other_formula.n_variables(), other_formula.n_clauses() - other_formula.satisfied_clauses());
        std::vector<int> next_clause;
        for(int i = 0; i < other_formula.n_clauses(); ++i) {
            if(other_formula.is_satisfied(i)) continue;
            next_clause.clear();
            bool satisfied = false;
            for(int j = 0; j < other_formula.clause_size(i); ++j) {
                const int lit = other_formula.literal_at_clause_pos(i, j);
                const int assigned = other_formula.assigned(lit);
                satisfied = satisfied || (assigned == 1);
                if(assigned == 0) next_clause.push_back(lit);
            }
            if(!satisfied) add_clause(next_clause);
        }
    }

    /**
     * Reserves space in the data structure.
     *
     * @param n variables
     * @param m clauses
     */
    void reserve(int n, int m) {
        number_of_variables = n;
        clauses_pt.reserve(m);
        clauses.reserve(3*m);
        variable_used_list.resize(n);
        variable_to_nclauses.reserve(n);
        clause_db_arbitrary.reserve(m);
        clause_db_size2.reserve(m);
        //clause_db_size3.reserve(2*m);
        for(int i = 0; i < n; ++i) {
            variable_to_nclauses.emplace_back(0, 0);
        }
    }

    /**
     * Add clause to the hash sets.
     *
     * @param clause the clause
     * @return whether the clause was actually added.
     */
    bool write_db(std::vector<int>& clause) {
        static std::vector<int> temporary_clause;
        std::vector<int>* use_clause;
        if(keep_original_order) {
            temporary_clause = clause;
            std::sort(temporary_clause.begin(), temporary_clause.end());
            temporary_clause.erase( unique( temporary_clause.begin(), temporary_clause.end() ), temporary_clause.end() );
            use_clause = &temporary_clause;
        } else {
            use_clause = &clause;
        }

        // we're adding the clause, we are gonna update the hash tables in any case
        if (use_clause->size() == 2) {
            return !clause_db_size2.insert({(*use_clause)[0], (*use_clause)[1]}).second;
        } else if (use_clause->size() == 3) {
            return !clause_db_size3.insert({(*use_clause)[0], (*use_clause)[1], (*use_clause)[2]}).second;
        } else {
            return !clause_db_arbitrary.insert((*use_clause)).second;
        }
    }

    /**
     * Checks whether clause is contained in the hash sets.
     *
     * @param clause
     * @return whether clause is contained
     */
    bool read_db(std::vector<int>& clause) const {
        // if we're not adding the clause, try to use sequential search
        int min_v = -1;
        int min_v_size = INT32_MAX;
        for (const auto l: clause) {
            const int v = abs(l) - 1;
            const int sz = variable_used_list[v].size();
            if (sz < min_v_size) {
                min_v = v;
                min_v_size = sz;
            }
        }
        if (min_v != -1 && min_v_size < 128 && !keep_original_order) {
            for(auto const c : variable_used_list[min_v]) {
                auto const [pt_start, pt_end] = clauses_pt[c];
                if(pt_end - pt_start != static_cast<int>(clause.size())) continue;
                int j = 0;
                for(int i = pt_start; i < pt_end; ++i) {
                    if(clauses[i] != clause[j]) break;
                    ++j;
                }
                if(j == static_cast<int>(clause.size())) return true;
            }
            return false;
        }
        if(clause.size() == 2) {
            const std::pair<int, int> check_pair = {clause[0], clause[1]};
            return clause_db_size2.find(check_pair) != clause_db_size2.end();
        } else if(clause.size() == 3) {
            const std::tuple<int, int, int> check_triple = {clause[0], clause[1], clause[2]};
            return clause_db_size3.find(check_triple) != clause_db_size3.end();
        } else {
            return clause_db_arbitrary.find(clause) != clause_db_arbitrary.end();
        }
    }

    /**
     * Add a clause to the data structure.
     *
     * @param clause
     */
    void add_clause(std::vector<int>& clause) {
        if(!keep_original_order) {
            std::sort(clause.begin(), clause.end());
            clause.erase( unique( clause.begin(), clause.end() ), clause.end() );
        }

        if(write_db(clause)) {
            [[unlikely]]
            ++removed_duplicate_clauses;
            return;
        }

        const int clause_number = clauses_pt.size();
        clauses_pt.emplace_back(clauses.size(), clauses.size() + clause.size());
        clauses.insert(clauses.end(), clause.begin(), clause.end());
        for(auto& l : clause) {
            assert(l != 0);
            const int v = abs(l) - 1;
            assert(v >= 0);
            assert(v < number_of_variables);
            if(l > 0) {
                variable_to_nclauses[v].first += 1;
            } else {
                variable_to_nclauses[v].second += 1;
            }
            variable_used_list[v].push_back(clause_number);
        }
    }

    /**
     * Tries to complete a given automorphism by extending it to negative literals.
     *
     * @param domain_size
     * @param automorphism
     * @return
     */
    bool complete_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
        support_test.initialize(domain_size);

        assert(automorphism.nsupp() < domain_size);
        for(int i = 0; i < automorphism.nsupp(); ++i) {
            assert(i >= 0);
            assert(i <= automorphism.nsupp());
            assert(automorphism.supp()[i] >= 0);
            assert(automorphism.supp()[i] < domain_size);
            support_test.set(automorphism.supp()[i]);
        }

        add_pairs.clear();
        for(int j = 0; j < automorphism.nsupp(); ++j) {
            const int i = automorphism.supp()[j];
            const int nv = sat_to_graph(-graph_to_sat(i));
            if(support_test.get(i) && !support_test.get(nv)) {
                const int npv = sat_to_graph(-graph_to_sat(automorphism.p()[i]));
                if(support_test.get(npv)) return false;
                //automorphism.write_single_map(nv, npv);
                add_pairs.emplace_back(nv, npv);
            }
        }

        for(auto p : add_pairs) {
            assert(p.first < domain_size);
            assert(p.second < domain_size);
            automorphism.write_single_map(p.first, p.second);
        }

        return true;
    }

    /**
     * Check whether supposed automorphism is a bijection.
     *
     * @param scratch_set
     * @param p
     * @param supp
     * @param supp_arr
     * @return
     */
    static bool cycle_check(dejavu::ds::markset& scratch_set, const int *p, int supp, const int *supp_arr) {
        scratch_set.reset();
        bool comp = true;
        for(int i = 0; i < supp && comp; ++i) {
            const int v = supp_arr[i];
            if(scratch_set.get(v)) continue;
            int v_next = p[v];
            while(v_next != v && comp) {
                comp = !scratch_set.get(v_next);
                scratch_set.set(v_next);
                v_next = p[v_next];
            }
        }
        return comp;
    }

    int vertex_variable_occurence(int v) {
        return variable_used_list[abs(graph_to_sat(v)) - 1].size();
    }

    /**
     * Test whether given map is an automorphism of the formula.
     *
     * @param domain_size
     * @param automorphism supposed automorphism
     * @return whether `automorphism` is indeed an automorphism of the formula represented by the datastructure
     */
    bool is_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
        test_used.initialize(n_clauses());
        support_test.initialize(domain_size);
        need_to_test_clauses.clear();

        cycle_check(support_test, automorphism.p(), automorphism.nsupp(), automorphism.supp());
        support_test.reset();

        assert(automorphism.nsupp() <= domain_size);
        for(int i = 0; i < automorphism.nsupp(); ++i) {
            assert(i >= 0);
            assert(i <= automorphism.nsupp());
            assert(automorphism.supp()[i] >= 0);
            assert(automorphism.supp()[i] < domain_size);

            support_test.set(automorphism.supp()[i]);
            const int v = abs(graph_to_sat(automorphism.supp()[i])) - 1;
            for(auto c : variable_used_list[v]) {
                if(!test_used.get(c)) {
                    need_to_test_clauses.push_back(c);
                    test_used.set(c);
                }
            }
        }

        test_used.reset();

        for(int j = 0; j < automorphism.nsupp(); ++j) {
            const int i = automorphism.supp()[j];
            const int nv = sat_to_graph(-graph_to_sat(i));
            const int nvp = automorphism.p()[nv];
            const int p  = automorphism.p()[i];
            const int pn = sat_to_graph(-graph_to_sat(p));
            if(nvp != pn) return false;
            if(!support_test.get(nv)) return false;
        }

        for(auto c : need_to_test_clauses) {
            test_clause.clear();
            bool all_identity = true;

            for (int j = 0; j < clause_size(c); ++j) {
                int l = literal_at_clause_pos(c, j);
                const int graph_literal = sat_to_graph(l);

                if(support_test.get(graph_literal)) {
                    all_identity = false;
                    int image_vert = automorphism.p()[graph_literal];
                    int image_literal = graph_to_sat(image_vert);
                    test_clause.push_back(image_literal);
                } else {
                    test_clause.push_back(l);
                }
            }

            if(all_identity) continue;
            std::sort(test_clause.begin(), test_clause.end());

            int j = 0;
            for (; j < clause_size(c); ++j) if(test_clause[j] != literal_at_clause_pos(c, j)) break;
            if(j == clause_size(c)) continue;

            if(!read_db(test_clause)) return false;
        }

        return true;
    }

    int literal_to_number_of_clauses(int l) {
        const int v = abs(l) - 1;
        if(l > 0) {
            return variable_to_nclauses[v].first;
        } else {
            return variable_to_nclauses[v].second;
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

    int n_duplicate_clauses_removed() {
        return removed_duplicate_clauses;
    }

    int n_variables() {
        return number_of_variables;
    }

    void clear_db() {
        clause_db_arbitrary = tsl::robin_set<std::vector<int>, any_hash>();
        clause_db_size2     = tsl::robin_set<std::pair<int, int>, pair_hash>();
        clause_db_size3     = tsl::robin_set<std::tuple<int, int, int>, triple_hash>();
    }

    void dimacs_output_clauses(std::ostream& out) {
        for(int i = 0; i < n_clauses(); ++i) {
            for (int j = 0; j < clause_size(i); ++j) {
                const int l = literal_at_clause_pos(i, j);
                out << l << " ";
            }
            out << "0" << "\n";
        }
    }

    void dimacs_output_clauses_unlocked(FILE* out) {
        constexpr int buffer_size = 16;
        char          buffer[buffer_size];

        for(int i = 0; i < n_clauses(); ++i) {
            for (int j = 0; j < clause_size(i); ++j) {
                const int l = literal_at_clause_pos(i, j);
                auto const [end_ptr, err] = std::to_chars(buffer, buffer + buffer_size, l);
                for(char* ptr = buffer; ptr < end_ptr; ++ptr) satsuma_putc(*ptr, out);
                satsuma_putc(' ', out);
            }
            satsuma_putc('0', out);
            satsuma_putc('\n', out);
        }
    }
};

#endif //SATSUMA_CNF_H
