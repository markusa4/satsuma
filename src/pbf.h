// Copyright 2026 Markus Anders
// This file is part of satsuma 1.4.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PBF_H
#define SATSUMA_PBF_H

#include <string>
#include "dejavu/groups.h"
#include "proof.h"
#include "tsl/robin_set.h"
#include "tsl/robin_map.h"
#include "utility.h"
#include "formula.h"


enum constraint_type { EQ, LEQ, OBJ };
 
/**
 * A PB formula with a hash table of clauses. Can not contain duplicate clauses.
 */
class pbf : public abstract_formula {
    // hash coefficients
    tsl::robin_map<std::string, int> coefficient_to_id;
    std::vector<std::string>         id_to_coefficient;
    int next_coeff_id = 0;

    int coefftoid(const std::string& coeff) {
        auto search_coeff = coefficient_to_id.find(coeff);
        if(search_coeff == coefficient_to_id.end()) {
            const int id = next_coeff_id++;
            coefficient_to_id.insert({coeff, id});
            id_to_coefficient.push_back(coeff);
            assert(id_to_coefficient[coefficient_to_id[coeff]] == coeff);
            return id;
        } else {
            assert(id_to_coefficient[search_coeff->second] == coeff);
            return search_coeff->second;
        }
    }

    // hash sets for clauses
    tsl::robin_set<std::vector<std::pair<int, int>>, any_hash2> clause_db_arbitrary_leq;
    tsl::robin_set<std::vector<std::pair<int, int>>, any_hash2> clause_db_arbitrary_eq;
    tsl::robin_set<std::vector<std::pair<int, int>>, any_hash2> clause_db_arbitrary_obj;
    bool opt   = false;
    int  n_leq = 0;
    int  n_eq  = 0;

    // clauses as a vector
    std::vector<std::pair<int, int>> clauses_pt;
    std::vector<int> clauses;
    // coeff IDs as a vector
    std::vector<int> coeffs;
    // right hand sides
    std::vector<int>             clause_to_rhs;
    std::vector<constraint_type> clause_to_type;

    // used lists
    std::vector<std::pair<int, int>> variable_to_nclauses;
    std::vector<std::vector<int>>    variable_used_list;

    // statistics
    int number_of_variables       = 0;
    int original_equal            = 0;
    int original_intsize          = 0;
    int removed_duplicate_clauses = 0;
    int removed_duplicate_eqs     = 0;

    // auxiliary data structures used for methods
    dejavu::ds::markset test_used;
    dejavu::ds::markset support_test;
    std::vector<int>    need_to_test_clauses;
    std::vector<std::pair<int, int>> test_pb_constraint;
    std::vector<std::pair<int, int>> add_pairs;

    // maintain the original order of literals in clauses
    bool keep_original_order = true;

public:
    /**
     * Reserves space in the data structure.
     *
     * @param n variables
     * @param m clauses
     */
    void reserve(int n, int m, int equal, int intsize) {
        number_of_variables = n;
        clauses_pt.reserve(m);
        clauses.reserve(3*m);
        variable_used_list.resize(n);
        variable_to_nclauses.reserve(n);
        clause_db_arbitrary_leq.reserve(m);
        clause_db_arbitrary_eq.reserve(m);
        clause_db_arbitrary_obj.reserve(1);
        for(int i = 0; i < n; ++i) {
            variable_to_nclauses.emplace_back(0, 0);
        }

        original_equal   = equal;
        original_intsize = intsize;
    }

    /**
     * Add clause to the hash sets.
     *
     * @param clause the clause
     * @return whether the clause was actually added.
     */
    bool write_db(std::vector<std::pair<int, int>>& pb_constraint, constraint_type ct) {
        // sort
        sort(pb_constraint.begin(), pb_constraint.end(), [](const auto& x, const auto& y){return x.first < y.first || (x.first == y.first && x.second < y.second);});
        switch(ct) {
            case LEQ:
                return !clause_db_arbitrary_leq.insert(pb_constraint).second;
            case EQ:
                return !clause_db_arbitrary_eq.insert(pb_constraint).second;
            case OBJ:
                return !clause_db_arbitrary_obj.insert(pb_constraint).second;
        }
        return false;
    }

    /**
     * Checks whether clause is contained in the hash sets.
     *
     * @param clause
     * @return whether clause is contained
     */
    bool read_db(std::vector<std::pair<int, int>>& pb_constraint, constraint_type ct) const {
        sort(pb_constraint.begin(), pb_constraint.end(), [](const auto& x, const auto& y){return x.first < y.first || (x.first == y.first && x.second < y.second);});
        switch(ct) {
            case LEQ:
                return clause_db_arbitrary_leq.find(pb_constraint) != clause_db_arbitrary_leq.end();
            case EQ:
                return clause_db_arbitrary_eq.find(pb_constraint) != clause_db_arbitrary_eq.end();
            case OBJ:
                return clause_db_arbitrary_obj.find(pb_constraint) != clause_db_arbitrary_obj.end();
        }
        return false;
    }

    /**
     * Add a clause to the data structure.
     *
     * @param clause
     *
     * @return whether clause was added (true) or not (false)
     */
    bool add_constraint(std::vector<int>& literals, std::vector<std::string>& coefficients, const std::string& rhs, 
                        constraint_type ct = LEQ) {
        static std::vector<int> coeff_ids;
        static std::vector<std::pair<int, int>> construct_pb;
        construct_pb.clear();
        coeff_ids.clear();

        opt = opt || (ct == constraint_type::OBJ);

        // construct a uniquely identifying vector
        for(size_t i = 0; i < literals.size(); i++) {
            const int coeff_id = coefftoid(coefficients[i]);
            construct_pb.push_back({coeff_id, literals[i]});
            coeff_ids.push_back(coeff_id);
        }
        construct_pb.push_back({coefftoid(rhs), 0});

        if(write_db(construct_pb, ct)) {
            [[unlikely]]
            removed_duplicate_clauses += 1;
            removed_duplicate_eqs     += (ct == EQ);
            return false;
        }

        n_leq += (ct == LEQ);
        n_eq  += (ct == EQ);

        const int clause_number = clauses_pt.size();
        clauses_pt.emplace_back(clauses.size(), clauses.size() + literals.size());
        clauses.insert(clauses.end(), literals.begin(), literals.end());
        coeffs.insert(coeffs.end(), coeff_ids.begin(), coeff_ids.end());
        clause_to_rhs.push_back(coefftoid(rhs));
        clause_to_type.push_back(ct);

        for(auto& l : literals) {
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
        return true;
    }

    /**
     * Tries to complete a given automorphism by extending it to negative literals.
     *
     * @param domain_size
     * @param automorphism
     * @return
     */
    virtual bool complete_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
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
    virtual bool is_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
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
            if(nvp != pn) {
                return false;
            }
            if(!support_test.get(nv)) {
                return false;
            }
        }

        for(auto c : need_to_test_clauses) {
            test_pb_constraint.clear();
            bool all_identity = true;

            for (int j = 0; j < clause_size(c); ++j) {
                int l = literal_at_clause_pos(c, j);
                int coeff = coeff_at_clause_pos(c, j);
                const int graph_literal = sat_to_graph(l);

                if(support_test.get(graph_literal)) {
                    all_identity = false;
                    int image_vert = automorphism.p()[graph_literal];
                    int image_literal = graph_to_sat(image_vert);
                    test_pb_constraint.push_back({coeff, image_literal});
                } else {
                    test_pb_constraint.push_back({coeff, l});
                }
            }
            // rhs
            test_pb_constraint.push_back({clause_to_rhs[c], 0});

            if(all_identity) continue;
            //std::sort(test_clause.begin(), test_clause.end());

            //int j = 0;
            //for (; j < clause_size(c); ++j) if(test_clause[j] != literal_at_clause_pos(c, j)) break;
            //if(j == clause_size(c)) continue;

            if(!read_db(test_pb_constraint, type_of_constraint(c))) {
                return false;
            }
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

    int rhs(int c) {
        return clause_to_rhs[c];
    }

    constraint_type type_of_constraint(int c) {
        return clause_to_type[c];
    }

    int literal_at_clause_pos(int c, int i) {
        return clauses[clauses_pt[c].first + i];
    }

    int coeff_at_clause_pos(int c, int i) {
        return coeffs[clauses_pt[c].first + i];
    }

    int n_total_clause_size() {
        return clauses.size();
    }

    int n_len() {
        return clauses.size();
    }

    virtual int n_clauses() {
        return clauses_pt.size();
    }

    bool is_optimization() {
        return opt;
    }

    int n_leq_constraints() {
        return n_leq;
    }

    int n_eq_constraints() {
        return n_eq;
    }

    int n_intsize() {
        return original_intsize;
    }

    int n_duplicate_clauses_removed() {
        return removed_duplicate_clauses;
    }

    int n_duplicate_eqs_removed() {
        return removed_duplicate_eqs;
    }

    virtual int n_variables() {
        return number_of_variables;
    }

    int n_coeffs() {
        return next_coeff_id;
    }

    void clear_db() {
        clause_db_arbitrary_leq = tsl::robin_set<std::vector<std::pair<int, int>>, any_hash2>();
        clause_db_arbitrary_eq  = tsl::robin_set<std::vector<std::pair<int, int>>, any_hash2>();
    }


    void dimacs_output_pb_constraints_unlocked(FILE* out) {
        for(int i = 0; i < n_clauses(); ++i) {
            if(type_of_constraint(i) == OBJ)  {
                satsuma_putc('m', out);
                satsuma_putc('i', out);
                satsuma_putc('n', out);
                satsuma_putc(':', out);
                satsuma_putc(' ', out);
            }

            for (int j = 0; j < clause_size(i); ++j) {
                // coefficient 
                output_string(out, id_to_coefficient[coeff_at_clause_pos(i, j)]);
                satsuma_putc(' ', out);

                // variable
                const int l = literal_at_clause_pos(i, j);
                if(l < 0) satsuma_putc('~', out);
                satsuma_putc('x', out);
                output_integer(out, abs(l));
                satsuma_putc(' ', out);
            }

            if(type_of_constraint(i) == OBJ) {
                satsuma_putc(' ', out);
                satsuma_putc(';', out);
                satsuma_putc('\n', out);
                continue;
            }

            if(type_of_constraint(i) == LEQ) satsuma_putc('>', out);
            satsuma_putc('=', out);
            satsuma_putc(' ', out);

            // rhs
            output_string(out, id_to_coefficient[rhs(i)]);
            satsuma_putc(' ', out);
            satsuma_putc(';', out);
            satsuma_putc('\n', out);
        }
    }

    void dimacs_output_knf_unlocked(FILE* out) {
        for(int i = 0; i < n_clauses(); ++i) {
            if(type_of_constraint(i) == EQ)  {
                satsuma_putc('k', out);
                satsuma_putc(' ', out);
                output_string(out, id_to_coefficient[rhs(i)]);
                satsuma_putc(' ', out);
            }

            for (int j = 0; j < clause_size(i); ++j) {
                // variable
                const int l = literal_at_clause_pos(i, j);
                if(l < 0) satsuma_putc('-', out);
                output_integer(out, abs(l));
                satsuma_putc(' ', out);
            }
            satsuma_putc('0', out);
            satsuma_putc('\n', out);
        }
    }
};

#endif //SATSUMA_PBF_H
