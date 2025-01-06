// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PREDICATE_H
#define SATSUMA_PREDICATE_H

#include <vector>
#include "proof.h"
#include <charconv>
#include "dejavu/dejavu.h"
#include "utility.h"

/**
 * Used to construct and store symmetry breaking predicates.
 */
class predicate {
    std::vector<std::vector<int>> sbp;
    std::vector<int> global_order_prefix;
    std::vector<int> global_order;
    std::vector<int> lit_to_order_pos;
    dejavu::markset  in_global_order;
    dejavu::markset  store_helper;

    std::vector<int> order_cache;
    std::vector<int> order_support;
    std::vector<int> vars_to_break_on;
    std::vector<dejavu::groups::stored_automorphism> generator_cache;

    int extra_variables = 0;
    int variables = 0;
    dejavu::groups::automorphism_workspace aw;

    proof_veripb* my_proof = nullptr;

    bool finalized_order = false;

    /**
     * Introduce an additional variable.
     * @return the fresh variable
     */
    int add_variable() {
        ++extra_variables;
        return variables + extra_variables;
    }

    void update_order_cache() {
        if(global_order.size() + global_order_prefix.size() != order_cache.size()) {
            order_cache.reserve(global_order.size() + global_order_prefix.size());
            order_cache = global_order_prefix;
            order_cache.insert(order_cache.end(), global_order.begin(), global_order.end());

            // update inverse order
            int global_pos = 1;
            for(int i = 0; i < static_cast<int>(global_order_prefix.size()); ++i) {
                const int lit = global_order_prefix[i];
                lit_to_order_pos[lit]               =  global_pos;
                lit_to_order_pos[graph_negate(lit)] = -global_pos;
                ++global_pos;
            }
            for(int i = 0; i < static_cast<int>(global_order.size()); ++i) {
                const int lit = global_order[i];
                lit_to_order_pos[lit]               =  global_pos;
                lit_to_order_pos[graph_negate(lit)] = -global_pos;
                ++global_pos;
            }
        }
    }

public:

    /**
     * Initialize an empty predicate, where \p nv is the number of variables of the original formula.
     *
     * @param nv Number of variables in the original formula.
     */
    predicate(int nv, proof_veripb* proof = nullptr) {
        in_global_order.initialize(2*nv);
        aw.resize(2*nv);
        lit_to_order_pos.resize(2*nv);
        allowed_lits.initialize(2*nv);
        store_helper.initialize(2*nv);
        variables = nv;
        my_proof = proof;
    }

    void assert_in_global_order(dejavu::groups::automorphism_workspace& automorphism) {
        for(int j = 0; j < automorphism.nsupp(); ++j) {
            assert(is_ordered(automorphism.supp()[j]));
        }
    };

    void add_to_global_order(const std::vector<int>& order, bool in_prefix = false) {
        for(auto v : order) {
            add_to_global_order(v, in_prefix);
        }
    }

    std::pair<int, int> get_inverse_order(int lit) {
        const int pos = lit_to_order_pos[lit];
        return {pos>0?lit:(sat_to_graph(-graph_to_sat(lit))), abs(pos)};
    }

    void add_to_global_order(int v, bool in_prefix = false) {
        if(!in_global_order.get(v) && !in_global_order.get(sat_to_graph(-graph_to_sat(v)))) {
            //const int pos_literal = sat_to_graph(abs(graph_to_sat(v)));
            const int pos_literal = v;
            if(in_prefix) global_order_prefix.push_back(pos_literal);
            else {
                global_order.push_back(pos_literal);
                order_cache.push_back(pos_literal);
                lit_to_order_pos[pos_literal]                               =   order_cache.size();
                lit_to_order_pos[sat_to_graph(-graph_to_sat(pos_literal))]  = -(order_cache.size());
            }
            in_global_order.set(pos_literal);
        }
    }

    dejavu::markset allowed_lits;

    /**
     * NOTE: This method is a mildly altered version of a similar method in BreakID.
     *
     * @param automorphism
     * @param order
     * @param extra_constraint_limt
     * @return
     */
    std::vector<int> determine_break_order(dejavu::groups::automorphism_workspace& automorphism,
                                               std::vector<int>& order, std::vector<int>& result,
                                               int extra_constraint_limt = INT32_MAX) {
        allowed_lits.reset();
        for (int i = order.size(); i > 0; --i) {
            int lit = order[i-1];
            if (!allowed_lits.get(lit)) {
                int sym = automorphism.p()[lit];

                while (sym != lit) { // add the other lits of the cycle and the negated cycle
                    allowed_lits.set(sym);
                    allowed_lits.set(graph_negate(sym));
                    sym = automorphism.p()[sym];
                }
            }
        }

        result.clear();
        result.reserve(std::min((int) order.size(), extra_constraint_limt));
        for (auto l: order) {
            int sym = automorphism.p()[l];
            if (l != sym && allowed_lits.get(l)) { result.push_back(graph_to_sat(l)); }
            if (graph_to_sat(sym) == -graph_to_sat(l)) { break; }
            if(static_cast<int>(result.size()) >= extra_constraint_limt){ break; }
        }

        return result;
    }

    void order_from_support(dejavu::groups::automorphism_workspace& automorphism, std::vector<int>& order) {
        std::vector<std::pair<int, int>> order_support;
        allowed_lits.reset();
        order_support.reserve(automorphism.nsupp());
        for(int i = 0; i < automorphism.nsupp(); ++i) {
            const int lit = automorphism.supp()[i];
            if(!allowed_lits.get(lit)) {
                order_support.emplace_back(get_inverse_order(lit));
                allowed_lits.set(lit);
                allowed_lits.set(graph_negate(lit));
            }
        }

        std::sort(order_support.begin(), order_support.end(), [](auto &left, auto &right) {
            return left.second < right.second;
        });

        order.clear();
        for (auto const& [l, ord]: order_support) {
            order.push_back(l);
        }
    }

    std::vector<int>& get_global_order() {
        return global_order;
    }

    bool is_ordered(int v) {
        return (in_global_order.get(v) || in_global_order.get(sat_to_graph(-graph_to_sat(v))));
    }

    void finalize_order() {
        if(finalized_order) terminate_with_error("trying to finalize order twice");
        update_order_cache();
        if(my_proof) my_proof->load_order_preamble(order_cache, variables);
        finalized_order = true;
        if (generator_cache.size() > 0)
            std::clog << "c\t writing " << generator_cache.size() << " deferred generators" << std::endl;
        for(size_t i = 0; i < generator_cache.size(); ++i) {
            generator_cache[i].load(aw);
            add_lex_leader_predicate(aw, {}, INT32_MAX);
        }

        generator_cache.clear();
    }

    /**
     * NOTE: This method is a mildly altered version of a similar method in BreakID.
     *
     * Adds lex-leader symmetry breaking constraints for automorphism, under a global order of variables.
     *
     * @param automorphism
     * @param order suggested order to extend the global order (conflicting orders are ignored)
     */
    void add_lex_leader_predicate(dejavu::groups::automorphism_workspace& automorphism,
                                  const std::vector<int>& order, int suggest_depth = 50) {
        if(!finalized_order) add_to_global_order(order);

        // delay actual generation in case we are proof logging
        if(!finalized_order && my_proof) {
            generator_cache.emplace_back();
            generator_cache.back().store(2*variables, automorphism, store_helper);
            return;
        }

        assert_in_global_order(automorphism);

        //if(!formula.is_automorphism(2*formula.n_variables(), automorphism)){
        //    std::clog << "c ****WARNING skipping uncertified generator" << std::endl;
        //    return;
        //}

        int extra_constraints = 0;
        int prev_lit = 0;
        int prev_sym = 0;
        int prev_tst = 0; // previous tseitin

        update_order_cache();

        // reduce order to the only those literals, which occur in the support of the automorphism
        order_from_support(automorphism, order_support);

        // then determine the break order
        determine_break_order(automorphism, order_support, vars_to_break_on, suggest_depth);

        if(my_proof) my_proof->lex_leader_dominance(automorphism, order_support);

        prev_tst = add_variable();
        sbp.push_back({prev_tst});
        if(my_proof) my_proof->lex_leader_tseitin(sbp.back(), prev_tst);

        //for (auto l: vars_to_break_on) {
        for (size_t i = 0; i < order_support.size(); ++i) {
            const int l = graph_to_sat(order_support[i]);
            const int sym = graph_to_sat(automorphism.p()[sat_to_graph(l)]);
            int tst = 0;

            // we continue logging, not outputting further breaking constraints
            const bool only_logging = i >= vars_to_break_on.size();

            // no need to continue only logging, when we are, in fact, not logging
            if(only_logging && !my_proof) break;

            if(extra_constraints == 0) {
                if(!only_logging) sbp.push_back({-l, sym});
                if (my_proof) my_proof->lex_leader_clause(sbp.back());
            } else {
                tst = add_variable();

                // output constraints if we are not only logging
                if(!only_logging) {
                    sbp.push_back({prev_sym, -prev_tst, tst});
                    sbp.push_back({-prev_lit, -prev_tst, tst});
                    //sbp.push_back({-tst, prev_tst});
                    //sbp.push_back({-tst, -prev_sym, prev_lit});
                    sbp.push_back({-tst, -l, sym});
                }

                // proof logging
                if(my_proof) {
                    my_proof->lex_leader_tseitin({prev_sym, -prev_tst, tst}, tst);
                    my_proof->lex_leader_tseitin({-prev_lit, -prev_tst, tst}, tst);
                    my_proof->lex_leader_tseitin({-tst, prev_tst}, -tst);
                    my_proof->lex_leader_tseitin({-tst, -prev_sym, prev_lit}, -tst);
                    my_proof->lex_leader_use_and_update_hint(prev_lit);
                    my_proof->lex_leader_clause({-tst, -l, sym});
                }

                prev_tst = tst;
            }

            ++extra_constraints;
            prev_lit = l;
            prev_sym = sym;
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

    void dimacs_output_clauses(FILE* out) {
        constexpr int buffer_size = 16;
        char          buffer[buffer_size];

        for(const auto& c : sbp) {
            for(const int l : c) {
                auto const [end_ptr, err] = std::to_chars(buffer, buffer + buffer_size, l);
                if(err == std::errc::value_too_large) terminate_with_error("buffer too small");
                for(char* ptr = buffer; ptr < end_ptr; ++ptr) satsuma_putc(*ptr, out);
                satsuma_putc(' ', out);
            }
            satsuma_putc('0', out);
            satsuma_putc('\n', out);
        }
    }
};

#endif //SATSUMA_PREDICATE_H
