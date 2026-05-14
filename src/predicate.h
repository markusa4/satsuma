// Copyright 2026 Markus Anders
// This file is part of satsuma 1.4.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PREDICATE_H
#define SATSUMA_PREDICATE_H

#include <vector>
#include "proof.h"
#include <charconv>
#include "dejavu/dejavu.h"
#include "utility.h"
#include "cnf.h"
#include "tracker.h"
#include <cstdint>

/**
 * Find disjoint direct components of group assuming separable generators. 
 * Currently, only used as an optimization for proof checking.
 *
 */
static void disjoint_components(int domain_size,
                                std::vector<dejavu::groups::stored_automorphism>& generators, 
                                dejavu::groups::automorphism_workspace& aw,
                                std::vector<std::vector<int>>& component_domains,
                                std::vector<std::vector<int>>& component_generators
                                ) {
    dejavu::groups::orbit domain_components(domain_size);

    // find the components assuming separable generators
    for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
        aw.reset();
        generators[j].load(aw);
        for(int i = 0; i < aw.nsupp(); ++i) {
            const int v0 = aw.supp()[0];
            const int vi = aw.supp()[i];
            domain_components.combine_orbits(v0, vi);
        }
    }

    // make component IDs
    dejavu::ds::markset    seen_this_component(domain_size);
    dejavu::ds::workspace  component_id(domain_size);
    int number_of_components = 0; // non-trivial ones

    std::vector<int> generator_to_component;
    generator_to_component.resize(generators.size());

    for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
        aw.reset();
        generators[j].load(aw);
        if(aw.nsupp() == 0) continue;
        const int v0 = aw.supp()[0];
        const int component_representative = domain_components.find_orbit(v0);
        if(!seen_this_component.get(component_representative)) {
            seen_this_component.set(component_representative);
            component_id[component_representative] = number_of_components;
            ++number_of_components;
        }
        generator_to_component[j] = component_id[component_representative];
    }

    // format output, make an iterable lists for each component

    component_domains.clear();
    component_domains.resize(number_of_components);
    for(int i = 0; i < domain_size; ++i) {
        const int component_representative = domain_components.find_orbit(i);
        if(seen_this_component.get(component_representative)) {
            const int component = component_id[component_representative];
            component_domains[component].push_back(i);
        }
    }

    component_generators.clear();
    component_generators.resize(number_of_components);
    for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
        const int component = generator_to_component[j];
            component_generators[component].push_back(j);
    }
}

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
    dejavu::ds::markset vars_to_break_on;
    std::vector<dejavu::groups::stored_automorphism> generator_cache;
    std::vector<int>                                 generator_cache_depth;

    int extra_variables = 0;
    int variables = 0;
    dejavu::groups::automorphism_workspace aw;

    proof* my_proof = nullptr;
    satsuma::tracker* track  = nullptr;

    // whether order was finalized
    bool finalized_order    = false;

    // write everything at once, at the end this is used for proof-logging, to enable splitting the order according 
    // to components
    bool write_at_once      = false;
    bool write_at_once_done = false;

    bool orbitopal_fixing       = false;
    bool orbitopal_fixing_only  = false;

    uint64_t dense_model_cost   = 0;
    uint64_t dense_model_budget = std::numeric_limits<uint64_t>::max();

    uint64_t sparse_model_cost   = 0;
    uint64_t sparse_model_budget = std::numeric_limits<uint64_t>::max();

    uint64_t order_model_cost   = 0;
    uint64_t order_model_budget = std::numeric_limits<uint64_t>::max();

    uint64_t used_generators = 0;
    uint64_t used_support    = 0;

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
    abstract_formula* formula = nullptr;

    /**
     * Initialize an empty predicate, where \p nv is the number of variables of the original formula.
     *
     * @param nv Number of variables in the original formula.
     */
    predicate(int nv, satsuma::tracker* track = nullptr, proof* proof = nullptr) {
        in_global_order.initialize(2*nv);
        aw.resize(2*nv);
        lit_to_order_pos.resize(2*nv);
        allowed_lits.initialize(2*nv);
        store_helper.initialize(2*nv);
        variables = nv;
        my_proof = proof;
        this->track = track;
        write_at_once = my_proof != nullptr;
        vars_to_break_on.initialize(2*nv);
    }

    void set_orbitopal_fixing(bool orbitopalFixing) {
        orbitopal_fixing = orbitopalFixing;
    }

    void set_orbitopal_fixing_only(bool orbitopalFixingOnly) {
        orbitopal_fixing_only = orbitopalFixingOnly;
    }

    void set_dense_model_budget(uint64_t budget) {
        dense_model_budget = budget;
    }

    void set_sparse_model_budget(uint64_t budget) {
        sparse_model_budget = budget;
    }

    void set_order_model_budget(uint64_t budget) {
        order_model_budget = budget;
    }

    void assert_in_global_order(dejavu::groups::automorphism_workspace& automorphism) {
        for(int j = 0; j < automorphism.nsupp(); ++j) {
            assert(is_ordered(automorphism.supp()[j]));
        }
    };

    bool add_to_global_order(const std::vector<int>& order, bool in_prefix = false) {
        bool all_succeeded = true;
        for(auto v : order) {
            const bool succeeded = add_to_global_order(v, in_prefix);
            all_succeeded = all_succeeded && succeeded;
        }
        return all_succeeded;
    }

    std::pair<int, int> get_inverse_order(int lit) {
        const int pos = lit_to_order_pos[lit];
        return {pos>0?lit:(sat_to_graph(-graph_to_sat(lit))), abs(pos)};
    }

    bool add_to_global_order(int v, bool in_prefix = false) {
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
            return true;
        }
        return false;
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
    int determine_break_order(dejavu::groups::automorphism_workspace& automorphism,
                                               std::vector<int>& order, 
                                               dejavu::ds::markset& result,
                                               int extra_constraint_limt = INT32_MAX) {
        allowed_lits.reset();
        for (int i = order.size(); i > 0; --i) {
            int lit = order[i-1];
            if (!allowed_lits.get(lit)) {
                int sym = automorphism[lit];

                while (sym != lit) { // add the other lits of the cycle and the negated cycle
                    allowed_lits.set(sym);
                    allowed_lits.set(graph_negate(sym));
                    sym = automorphism[sym];
                }
            }
        }

        result.reset();
        int count = 0;
        for (auto l: order) {
            int sym = automorphism[l];
            if (l != sym && allowed_lits.get(l)) {
                result.set(l);
                ++count;
            }
            if (graph_to_sat(sym) == -graph_to_sat(l)) 
                break;
            if(count >= extra_constraint_limt)
                break;
        }

        return count;
    }

    void filter_order_to_support(std::vector<int>& support, std::vector<int>& order) {
        std::vector<std::pair<int, int>> order_support;
        allowed_lits.reset();
        order_support.reserve(support.size());
        for(int i = 0; i < static_cast<int>(support.size()); ++i) {
            const int lit = support[i];
            if(!in_global_order.get(lit)) continue;
            order_support.emplace_back(get_inverse_order(lit));
        }

        std::sort(order_support.begin(), order_support.end(), [](auto &left, auto &right) {
            return left.second < right.second;
        });

        order.clear();
        for (auto const& [l, ord]: order_support) {
            order.push_back(l);
        }
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

    bool all_unordered(std::vector<int>& vars) {
        for(const auto& v : vars) {
            if(is_ordered(v)) return false;
        }
        return true;
    }

    void finalize_order() {
        if(finalized_order) terminate_with_error("trying to finalize order twice");
        update_order_cache();
        finalized_order = true;
    }

    void write_all_deferred(long order_limit = -1) {
        if(!write_at_once)        return;
        if(orbitopal_fixing_only) return;
        write_at_once = false;

        // we have already considered the budget while storing the generators
        dense_model_budget  = std::numeric_limits<uint64_t>::max();
        sparse_model_budget = std::numeric_limits<uint64_t>::max();
        order_model_cost    = 0;

        // std::clog << "c \twriting " << generator_cache.size() << " deferred generators" << std::endl;

        // I am bothered by this -- on a technical level, it seems there is no real need for the predicate to know 
        // about disjoint components, or having to split the order according to it
        // -- this is purely an optimization for proof *checking*
        std::vector<std::vector<int>> component_domains;
        std::vector<std::vector<int>> component_generators;
        
        disjoint_components(2*variables, generator_cache, aw, component_domains, component_generators);
        // std::clog << "c \tsplit order into " << component_domains.size() << " components" << std::endl;

        // now output symmetry breaking clauses and proof for each component separately
        std::vector<int> order_of_component;
        for(size_t component = 0; component < component_domains.size(); ++component) {
            // get the (partial) order for this component
            order_of_component.clear();
            filter_order_to_support(component_domains[component], order_of_component);

            // skip if exceeding the order limit
            if(order_limit >= 0 && order_limit < static_cast<long>(order_of_component.size())) continue;

            // in the proof, load the order for this component
            if(my_proof) my_proof->load_order(order_of_component, variables);
            
            // output symmetry breaking constraitns for generators of this component 
            for(size_t j = 0; j < component_generators[component].size(); ++j) {
                if(order_model_cost > order_model_budget) break;
                order_model_cost += order_of_component.size();

                aw.reset();
                const int i = component_generators[component][j];
                generator_cache[i].load(aw);
                const int depth = generator_cache_depth[i];
                add_lex_leader_predicate(aw, {}, depth); 
            }
        }

        // unload the order now
        if(my_proof) my_proof->unload_order();

        // clear auxiliary data structures
        generator_cache.clear();
        generator_cache_depth.clear();

        // make sure we don't write anything to the predicate anymore
        write_at_once      = true;
        write_at_once_done = true;
    }

    /**
     *
     * Adds lex-leader symmetry breaking constraints for automorphism, under a global order of variables.
     *
     * @param automorphism
     * @param order suggested order to extend the global order (conflicting orders are ignored)
     */
    void add_lex_leader_predicate(dejavu::groups::automorphism_workspace& automorphism,
                                  const std::vector<int>& order, int suggest_depth = 50) {
        if(!finalized_order) add_to_global_order(order);

        if(sparse_model_cost > sparse_model_budget || 
           dense_model_cost  > dense_model_budget) {
            //std::clog << "c \tignoring generator (predicate budget exceeded)" << std::endl;
            return;
        }

        // update internal cost tracker
        sparse_model_cost += automorphism.nsupp();
        dense_model_cost  += formula->n_clauses();


        // delay actual generation in case we are proof logging
        if(write_at_once) {
            generator_cache.emplace_back();
            generator_cache.back().store(2*variables, automorphism, store_helper);
            generator_cache_depth.push_back(suggest_depth);
            return;
        }

        if(write_at_once && write_at_once_done) 
            terminate_with_error("not allowed to write symmetry breaking clauses");

        assert_in_global_order(automorphism);

        if(orbitopal_fixing_only) {
            return; // TODO
        }

        //if(!formula->is_automorphism(2*formula->n_variables(), automorphism)){
        //    std::clog << "c ****WARNING skipping uncertified generator" << std::endl;
        //    return;
        //}

        // variables needed to make SBP
        int extra_constraints = 0;
        int prev_lit = 0;
        int prev_sym = 0;
        int prev_tst = 0; // previous tseitin

        update_order_cache();

        // statistics 
        used_generators += 1;
        used_support    += automorphism.nsupp();

        // reduce order to only those literals, which occur in the support of the automorphism
        order_from_support(automorphism, order_support);

        // then determine the break order
        int limit = determine_break_order(automorphism, order_support, vars_to_break_on, suggest_depth);
        // int limit = std::min(static_cast<int>(order_support.size()), suggest_depth);
        
        // artificially reduce limit for transposition
        if(order_support.size() == 2 && limit == 2) limit = 1;

        if(track) {
            track->add_to_metric(satsuma::SYM_LEX, 1);
            track->add_to_metric(satsuma::SYM_LEX_SUPPORT, limit);
        }

        const int tseitin_id_start = variables + extra_variables; // used later for proof logging
        //prev_tst = add_variable();
        //const int tseitin_id_start = prev_tst - 1; // used later for proof logging
        //sbp.push_back({prev_tst});

        for (size_t i = 0; i < order_support.size(); ++i) {
            const int l   = graph_to_sat(order_support[i]);
            const int sym = graph_to_sat(automorphism.p()[sat_to_graph(l)]);
            int tst = 0;

            // reached depth limit
            if(static_cast<int>(i) >= limit) break;

            if(extra_constraints == 0) {
                if(-l != sym)
                    sbp.push_back({-l, sym});
                else  { 
                    sbp.push_back({-l});
                }
            } else if (extra_constraints == 1) {
                tst = add_variable();

                // output constraints if we are not "only logging" this one
                sbp.push_back({prev_sym,  tst}); // (1)
                if(prev_sym != -prev_lit)
                    sbp.push_back({-prev_lit, tst}); // (2)
                if(-l != sym) {
                    sbp.push_back({-tst,      -l,        sym}); // (3)
                } else {
                    sbp.push_back({-tst,      -l}); // (3)
                }
                // sbp.push_back({-tst, prev_tst});            // (4) blocked clause (not needed)
                // sbp.push_back({-tst, -prev_sym, prev_lit}); // (5) blocked clause (not needed)
                prev_tst = tst;
            } else {
                tst = add_variable();

                // output constraints if we are not "only logging" this one
                sbp.push_back({prev_sym,  -prev_tst, tst}); // (1)
                if(prev_sym != -prev_lit)
                    sbp.push_back({-prev_lit, -prev_tst, tst}); // (2)
                if(-l != sym) {
                    sbp.push_back({-tst,      -l,        sym}); // (3)
                } else {
                    sbp.push_back({-tst,      -l}); // (3)
                }

                // sbp.push_back({-tst, prev_tst});            // (4) blocked clause (not needed)
                // sbp.push_back({-tst, -prev_sym, prev_lit}); // (5) blocked clause (not needed)
                prev_tst = tst;
            }

            ++extra_constraints;
            prev_lit = l;
            prev_sym = sym;
        }

        // proof logging
        if(my_proof) my_proof->sbp(automorphism, order_support, tseitin_id_start - 1, limit);
    }

    void add_propagation(int literal, int blocked_literal = 0, 
                         dejavu::groups::automorphism_workspace* reason = nullptr) {
        sbp.push_back({literal});
        if(my_proof && reason) my_proof->orbitopal_fixing(literal, blocked_literal, *reason);
        if(my_proof && !reason) my_proof->drat_clause({literal});
    }

    void add_propagation_pure(int literal) {
        sbp.push_back({literal});
        if(my_proof) my_proof->rup_clause({literal});
    }

    void add_binary_clause(int orbit_repr_literal, int other_literal,
                           dejavu::groups::automorphism_workspace& reason) {
        // if(orbitopal_fixing_only) return;
        sbp.push_back({-orbit_repr_literal, other_literal});
        if(my_proof) my_proof->binary_clause(-orbit_repr_literal, other_literal, reason);
    }
    

    void add_binary_clause_sr_log(int orbit_repr_literal, int other_literal,
                         dejavu::groups::automorphism_workspace& reason) {
        // sbp.push_back({-orbit_repr_literal, other_literal});
        if(my_proof) my_proof->binary_clause(orbit_repr_literal, -other_literal, reason);
    }

    /**
     * Get the total support of automorphisms used to make the predicate.
     *
     * @return support
     */
    uint64_t get_support() {
        return used_support;
    }

    /**
     * Get the total number of generators used to make the predicate.
     *
     * @return support
     */
    uint64_t get_generators() {
        return used_generators;
    }

    /**
     * Get the total number of generators used to make the predicate.
     *
     * @return support
     */
    std::vector<int>& get_clause(int i ) {
        return sbp[i];
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

    void dimacs_output_clauses(FILE* out) {
        for(const auto& c : sbp) {
            for(const int l : c) {
                output_integer(out, l);
                satsuma_putc(' ', out);
            }
            satsuma_putc('0', out);
            satsuma_putc('\n', out);
        }
    }

    void pb_output_clauses(FILE* out) {
        for(const auto& c : sbp) {
            for(const int l : c) {
                satsuma_putc('+', out);
                satsuma_putc('1', out);
                satsuma_putc(' ', out);
                if(l < 0) satsuma_putc('~', out);
                satsuma_putc('x', out);
                output_integer(out, abs(l));
                satsuma_putc(' ', out);
            }
            satsuma_putc('>', out);
            satsuma_putc('=', out);
            satsuma_putc(' ', out);
            satsuma_putc('+', out);
            satsuma_putc('1', out);
            satsuma_putc(' ', out);
            satsuma_putc(';', out);
            satsuma_putc('\n', out);
        }
    }
};

#endif //SATSUMA_PREDICATE_H
