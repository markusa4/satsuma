// Copyright 2024 Markus Anders
// This file is part of satsuma 1.0.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PREDICATE_H
#define SATSUMA_PREDICATE_H

#include <vector>
#include "dejavu/dejavu.h"
#include "utility.h"

/**
 * Used to construct and store symmetry breaking predicates.
 */
class predicate {
    std::vector<std::vector<int>> sbp;
    std::vector<int> global_order_prefix;
    std::vector<int> global_order;
    dejavu::markset  in_global_order;

    int extra_variables = 0;
    int variables = 0;
    dejavu::groups::automorphism_workspace aw;
    /**
     * Introduce an additional variable.
     * @return the fresh variable
     */
    int add_variable() {
        ++extra_variables;
        return variables + extra_variables;
    }

public:

    /**
     * Initialize an empty predicate, where \p nv is the number of variables of the original formula.
     *
     * @param nv Number of variables in the original formula.
     */
    predicate(int nv) {
        in_global_order.initialize(2*nv);
        aw.resize(2*nv);
        variables = nv;
    }

    void assert_in_global_order(dejavu::groups::automorphism_workspace& automorphism) {
        for(int j = 0; j < automorphism.nsupp(); ++j) {
            const int v = automorphism.supp()[j];
            assert(is_ordered(v));
        }
    };

    void add_to_global_order(std::vector<int>& order, bool in_prefix = false) {
        for(auto v : order) {
            add_to_global_order(v, in_prefix);
        }
    }

    void add_to_global_order(int v, bool in_prefix = false) {
        if(!in_global_order.get(v) && !in_global_order.get(sat_to_graph(-graph_to_sat(v)))) {
            //const int pos_literal = sat_to_graph(abs(graph_to_sat(v)));
            const int pos_literal = v;
            if(in_prefix) global_order_prefix.push_back(pos_literal);
            else global_order.push_back(pos_literal);
            in_global_order.set(pos_literal);
        }
    }

    /**
     * NOTE: This method is a mildly altered version of a similar method in BreakID.
     *
     * @param automorphism
     * @param order
     * @param extra_constraint_limt
     * @return
     */
    std::vector<int> determine_break_order(dejavu::groups::automorphism_workspace& automorphism,
                                            std::vector<int>& order, int extra_constraint_limt = INT32_MAX) {
        std::unordered_set<int> allowedLits; // which are not the last lit in their cycle, unless they map to their negation
        for (int i = order.size(); i > 0; --i) {
            int lit = order.at(i - 1);
            if (allowedLits.count(graph_to_sat(lit)) == 0) {
                int sym = automorphism.p()[lit];

                while (sym != lit) { // add the other lits of the cycle and the negated cycle
                    allowedLits.insert(graph_to_sat(sym));
                    allowedLits.insert(-graph_to_sat(sym));
                    sym = automorphism.p()[sym];
                }
            }
        }

        std::vector<int> result;
        result.reserve(order.size());
        for (auto l: order) {
            int sym = automorphism.p()[l];

            if (l != sym && allowedLits.count(graph_to_sat(l)) > 0) { result.push_back(graph_to_sat(l)); }
            if (graph_to_sat(sym) == -graph_to_sat(l)) { break; }
            if(static_cast<int>(result.size()) >= extra_constraint_limt){ break; }
        }
        return result;
    }

    std::vector<int>& get_global_order() {
        return global_order;
    }

    bool is_ordered(int v) {
        return (in_global_order.get(v) || in_global_order.get(sat_to_graph(-graph_to_sat(v))));
    }

    std::vector<int> order_cache;

    /**
     * NOTE: This method is a mildly altered version of a similar method in BreakID.
     *
     * Adds lex-leader symmetry breaking constraints for automorphism, under a global order of variables.
     *
     * @param automorphism
     * @param order suggested order to extend the global order (conflicting orders are ignored)
     */
    void add_lex_leader_predicate(dejavu::groups::automorphism_workspace& automorphism, std::vector<int>& order,
                                  int suggest_depth = 50) {
        add_to_global_order(order);
        assert_in_global_order(automorphism);

        int extra_constraints = 0;
        int prev_lit = 0;
        int prev_sym = 0;
        int prev_tst = 0; // previous tseitin

        if(global_order.size() + global_order_prefix.size() != order_cache.size()) {
            order_cache.reserve(global_order.size() + global_order_prefix.size());
            order_cache = global_order_prefix;
            order_cache.insert(order_cache.end(), global_order.begin(), global_order.end());
        }

        std::vector<int> varsToBreakOn = determine_break_order(automorphism, order_cache, suggest_depth);

        for (auto l: varsToBreakOn) {
            int sym = graph_to_sat(automorphism.p()[sat_to_graph(l)]);
            int tst = 0;
            if (extra_constraints == 0) {
                sbp.push_back({-l, sym});
            } else if (extra_constraints == 1) {
                tst = add_variable();
                sbp.push_back({-prev_lit, -l, sym});
                sbp.push_back({-prev_lit, tst});
                sbp.push_back({prev_sym, -l, sym});
                sbp.push_back({prev_sym, tst});
            } else {
                tst = add_variable();
                sbp.push_back({-prev_tst, -prev_lit, -l, sym});
                sbp.push_back({-prev_tst, -prev_lit, tst});
                sbp.push_back({-prev_tst, prev_sym, -l, sym});
                sbp.push_back({-prev_tst, prev_sym, tst});
            }

            ++extra_constraints;

            prev_lit = l;
            prev_sym = sym;
            prev_tst = tst;
        }
    }

    void add_binary_clause(int orbit_repr_literal, int other_literal) {
        sbp.push_back({-orbit_repr_literal, other_literal});
    }

    /**
     * Number of extra variables introduced by the predicate.
     *
     * @return number of extra variables
     */
    int n_extra_variables() {
        return extra_variables;
    }

    /**
     * Number of extra clauses introduced by the predicate.
     *
     * @return number of extra clauses
     */
    int n_clauses() {
        return sbp.size();
    }

    /**
     * Output the clauses of this predicate to the given output stream.
     *
     * @param out the output stream
     */
    void dimacs_output_clauses(std::ostream& out) {
        for(auto c : sbp) {
            for(auto l : c) {
                out << l << " ";
            }
            out << "0" << "\n";
        }
    }
};

#endif //SATSUMA_PREDICATE_H
