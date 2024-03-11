// Copyright 2024 Markus Anders
// This file is part of satsuma 1.0.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_CNF_H
#define SATSUMA_CNF_H

#include <string>
#include <unordered_map>
#include "utility.h"

class cnf {
private:
    // Hash function
    struct hashFunction
    {
        size_t operator()(const std::vector<int>
                          &myVector) const
        {
            std::hash<int> hasher;
            size_t answer = 0;

            for (int i : myVector)
            {
                answer ^= hasher(i) + 0x9e3779b9 +
                          (answer << 6) + (answer >> 2);
            }
            return answer;
        }
    };

    std::unordered_set<std::vector<int>, hashFunction> clause_duplicates;
    std::vector<std::pair<int, int>> clauses_pt;
    std::vector<int> clauses;
    std::vector<std::pair<int, int>> variable_to_nclauses;
    std::vector<std::vector<int>> variable_used_list;

    dejavu::markset test_used;
    int number_of_variables = 0;

public:
    void reserve(int n, int m) {
        number_of_variables = n;
        clauses_pt.reserve(m);
        clauses.reserve(4*m);
        variable_used_list.resize(n);
        variable_to_nclauses.reserve(n);
        for(int i = 0; i < n; ++i) {
            variable_to_nclauses.emplace_back(0, 0);
        }

    }

    bool test_clause_db(std::vector<int>& clause, bool add) {
        //std::ostringstream sstream;
        //for(auto& l : clause) sstream << l << " " << std::endl;
        //std::string str = sstream.str();
        bool test = clause_duplicates.find(clause) != clause_duplicates.end();
        if(!test && add) clause_duplicates.insert(clause);
        return test;
    }

    void add_clause(std::vector<int>& clause) {
        clause.erase( unique( clause.begin(), clause.end() ), clause.end() );
        std::sort(clause.begin(), clause.end());

        if(test_clause_db(clause, true)) return;

        const int clause_number = clauses_pt.size();
        clauses_pt.emplace_back(clauses.size(), clauses.size() + clause.size());
        clauses.insert(clauses.end(), clause.begin(), clause.end());
        for(auto& l : clause) {
            const int v = abs(l) - 1;
            if(l > 0) {
                variable_to_nclauses[v].first += 1;
            } else {
                variable_to_nclauses[v].second += 1;
            }
            variable_used_list[v].push_back(clause_number);
        }
    }

    dejavu::markset support_test;
    std::vector<int> need_to_test_clauses;
    std::vector<int> test_clause;
    std::vector<std::pair<int, int>> add_pairs;

    bool complete_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
        support_test.initialize(domain_size);
        need_to_test_clauses.clear();

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
            if(!test_clause_db(test_clause, false)) return false;
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
};

#endif //SATSUMA_CNF_H
