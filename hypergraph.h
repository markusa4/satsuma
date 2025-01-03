// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_HYPERGRAPH_H
#define SATSUMA_HYPERGRAPH_H

#include "cnf.h"
#include "tsl/robin_map.h"

namespace satsuma {
    class hypergraph_wrapper {
        std::vector<int> literal_to_binary_clauses;
        std::vector<int> literal_to_ternary_clauses;
        std::vector<int> literal_to_hyperedges;
        std::vector<int> literal_to_removed;
        std::vector<int> literal_iso_inv;
        std::vector<bool> clause_tombstone;

    public:
        cnf& wrapped_formula;
        std::vector<std::vector<int>> hyperedge_list;
        std::vector<int>              hyperedge_color;
        std::vector<std::pair<int, int>> hyperedge_inner_structure;
        std::vector<int>                 hyperedge_inner_degree;

        int binary_clauses     = 0;
        int ternary_clauses    = 0;

        int removed_clauses = 0;
        int removed_clause_support = 0;
        int hyperedge_support = 0;
        int hyperedge_inner_structure_support = 0;

        hypergraph_wrapper(cnf &formula) : wrapped_formula(formula) {
            // initialize trivial hypergraph wrapper (which does not change the underlying formula)
            literal_to_binary_clauses.resize(wrapped_formula.n_variables()*2);
            //literal_to_ternary_clauses.resize(wrapped_formula.n_variables()*2);
            literal_to_hyperedges.resize(wrapped_formula.n_variables()*2);
            literal_to_removed.resize(wrapped_formula.n_variables()*2);
            for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
                if(wrapped_formula.clause_size(i) == 2) {
                    literal_to_binary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0))] += 1;
                    literal_to_binary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1))] += 1;
                    ++binary_clauses;
                }

                if(wrapped_formula.clause_size(i) == 3) {
                    ++ternary_clauses;
                    //literal_to_ternary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0))] += 1;
                    //literal_to_ternary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1))] += 1;
                    //literal_to_ternary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 2))] += 1;
                }
            }
            clause_tombstone.resize(wrapped_formula.n_clauses());
        }

        int literal_to_number_of_binary_clauses(int literal) {
            return literal_to_binary_clauses[sat_to_graph(literal)];
        }

        int literal_to_number_of_hyperedges(int literal) {
            return literal_to_hyperedges[sat_to_graph(literal)];
        }

        int literal_to_number_of_removed_uses(int literal) {
            return literal_to_removed[sat_to_graph(literal)];
        }

        int hyperedge_to_extra_degree(int hyperedge) {
            return hyperedge_inner_degree[hyperedge];
        }

        //int literal_to_number_of_ternary_clauses(int literal) {
        //    return literal_to_ternary_clauses[sat_to_graph(literal)];
        //}


        int add_hyperedge(std::vector<int> hyperedge, int color) {
            for(auto& l : hyperedge) {
                ++literal_to_hyperedges[sat_to_graph(l)];
            }
            hyperedge_support += hyperedge.size();
            hyperedge_list.push_back(hyperedge);
            hyperedge_color.push_back(color);
            hyperedge_inner_degree.push_back(0);

            return hyperedge_list.size() - 1;
        }

        void add_to_hyperedge(int hyperedge, int add_literal) {
            ++literal_to_hyperedges[sat_to_graph(add_literal)];
            hyperedge_list[hyperedge].push_back(add_literal);
            ++hyperedge_support;
        }

        int add_hyperedge(std::vector<int> hyperedge, std::vector<int> inner_structure, int color) {
            const int myself = add_hyperedge(hyperedge, color);
            for (auto& h : inner_structure) {
                ++hyperedge_inner_degree[h];
                ++hyperedge_inner_degree[myself];
                hyperedge_inner_structure.push_back({h, myself});
                hyperedge_inner_structure_support += 1;
            }

            return myself;
        }



        void remove_clause(int i) {
            clause_tombstone[i] = true;
            for(int j = 0; j < wrapped_formula.clause_size(i); ++j) {
                ++literal_to_removed[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, j))];
            }
            removed_clause_support += wrapped_formula.clause_size(i);
            ++removed_clauses;
            if(wrapped_formula.clause_size(i) == 2) --binary_clauses;
        }

        bool is_clause_removed(int i) {
            return clause_tombstone[i];
        }

        int n_hyperedges() {
            return hyperedge_list.size();
        }

        unsigned long iso_inv(int literal) {
            unsigned long hash = hash32shift(wrapped_formula.literal_to_number_of_clauses(literal));
            hash = add_to_hash(hash, hash32shift(literal_to_number_of_binary_clauses(literal)));
            //hash = add_to_hash(hash, hash32shift(literal_to_number_of_ternary_clauses(literal)));
            hash = add_to_hash(hash, hash32shift(literal_iso_inv[sat_to_graph(literal)]));
            return hash;
        }

        void hypergraph_reduction() {
            // dejavu::groups::orbit orbits2(wrapped_formula.n_variables()*2);
            literal_iso_inv.resize(wrapped_formula.n_variables()*2);
            std::vector<int>  incident_binary;
            std::vector<int> incident_ternary;
            incident_binary.resize(wrapped_formula.n_variables()*2);
            incident_ternary.resize(wrapped_formula.n_variables()*2);
            tsl::robin_set<std::pair<int, int>, pair_hash> clause_tombstone2;
            tsl::robin_map<std::pair<int, int>, int, pair_hash> count_pairs_in_triples;

            for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
                if(wrapped_formula.clause_size(i) == 2) {
                    ++incident_binary[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0))];
                    ++incident_binary[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1))];

                }
                if(wrapped_formula.clause_size(i) == 2) {
                    ++incident_ternary[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0))];
                    ++incident_ternary[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1))];
                    ++incident_ternary[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 2))];
                }
            }

            int no_binary = 0;
            for(int i = 0; i < 2*wrapped_formula.n_variables(); i+=2) {
                if(incident_binary[i] == 0 && incident_binary[i+1] == 0) ++no_binary;
            }
            std::clog << "not incident to binary: " << no_binary << std::endl;

            std::clog << " (sz2=" << binary_clauses << ", sz3=" << ternary_clauses << ")" << std::endl;

            for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
                if (wrapped_formula.clause_size(i) != 3) continue;
                std::vector<int> clause_at_hand = {wrapped_formula.literal_at_clause_pos(i, 0),
                                                   wrapped_formula.literal_at_clause_pos(i, 1),
                                                   wrapped_formula.literal_at_clause_pos(i, 2)};
                std::sort(clause_at_hand.begin(), clause_at_hand.end());
                const int l1 = clause_at_hand[0];
                const int l2 = clause_at_hand[1];
                const int l3 = clause_at_hand[2];

                count_pairs_in_triples[{l1, l2}] = 0;
                count_pairs_in_triples[{l2, l3}] = 0;
                count_pairs_in_triples[{l1, l3}] = 0;
            }

            // ternary negation macro
            for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
                if (wrapped_formula.clause_size(i) != 3) continue;
                std::vector<int> clause_at_hand = {wrapped_formula.literal_at_clause_pos(i, 0),
                                                   wrapped_formula.literal_at_clause_pos(i, 1),
                                                   wrapped_formula.literal_at_clause_pos(i, 2)};
                std::sort(clause_at_hand.begin(), clause_at_hand.end());
                const int l1 = clause_at_hand[0];
                const int l2 = clause_at_hand[1];
                const int l3 = clause_at_hand[2];
                
                ++count_pairs_in_triples[{l1, l2}]; 
                ++count_pairs_in_triples[{l2, l3}]; 
                ++count_pairs_in_triples[{l1, l3}]; 
            }

            std::vector<std::pair<std::pair<int, int>, int>> uses;
            tsl::robin_map<std::pair<int, int>, int, pair_hash> pair_to_hyperedge;

            for(const auto& key_value : count_pairs_in_triples) {
                uses.push_back({key_value.first, key_value.second});
            }

            std::sort(uses.begin(), uses.end(), [](auto &left, auto &right) {
                return left.second > right.second;
            });

            constexpr int min_triple_replace = 8;


            if(uses.size() == 0) return;

            const int max_triple = uses[0].second;
            int triple_reductions = 0;
            if(max_triple > min_triple_replace) {
                std::vector<std::pair<int, int>> max_pairs;
                for(const auto& use : uses) {
                    if(use.second > min_triple_replace) {
                        pair_to_hyperedge[use.first] = -1;
                    }
                }

                for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
                    if (wrapped_formula.clause_size(i) != 3) continue;
                    std::vector<int> clause_at_hand = {wrapped_formula.literal_at_clause_pos(i, 0),
                                                       wrapped_formula.literal_at_clause_pos(i, 1),
                                                       wrapped_formula.literal_at_clause_pos(i, 2)};
                    std::sort(clause_at_hand.begin(), clause_at_hand.end());
                    const int l1 = clause_at_hand[0];
                    const int l2 = clause_at_hand[1];
                    const int l3 = clause_at_hand[2];

                    std::vector<std::pair<int, std::tuple<int, int, int>>> counts = {{count_pairs_in_triples[{l1, l2}], {l1, l2, l3}}, 
                                                               {count_pairs_in_triples[{l2, l3}], {l2, l3, l1}}, 
                                                               {count_pairs_in_triples[{l1, l3}], {l1, l3, l2}}};

                    std::sort(counts.begin(), counts.end(), [](auto &left, auto &right) {
                        return left.first < right.first;
                    });

                    const int large_triple = counts[2].first;
                    if(large_triple > min_triple_replace  && counts[1].first != large_triple && 
                                                      counts[0].first != large_triple) {
                        const std::pair<int, int> prev_edge = {std::get<0>(counts[2].second),std::get<1>(counts[2].second)};

                        if(pair_to_hyperedge[prev_edge] < 0) {
                            const int added_hyperedge        = add_hyperedge({prev_edge.first, prev_edge.second}, 3);
                            const int added_hyperedge_second = add_hyperedge({}, {added_hyperedge}, 4);
                            pair_to_hyperedge[prev_edge] = added_hyperedge_second;
                        }

                        ++triple_reductions;
                        add_to_hyperedge(pair_to_hyperedge[prev_edge], std::get<2>(counts[2].second));
                        remove_clause(i);
                    }
                }
            }
            
            for(int i = 0; i < 2*wrapped_formula.n_variables(); i += 2) {
                if(incident_ternary[i] + incident_ternary[i+1] > 200) {
                    std::clog << incident_ternary[i] << ", " << incident_ternary[i+1] << std::endl;
                }
            }
            std::clog << "potential max_triple(" << max_triple << ")reductions: " << triple_reductions << std::endl;



            std::clog << "c\t +hyedge=" << n_hyperedges() << ", +hyedge_sup=" << hyperedge_support << ", -cl=" << removed_clauses
                      << ", -cl_sup=" << removed_clause_support << std::endl;
            //std::clog << "c\t found " << replacement_possible.size() << " [clauses: " << potential_removed_clauses << "] potential hypergraph reductions" << std::endl;
        }

        void clear() {
            literal_to_binary_clauses.clear();
            literal_to_ternary_clauses.clear();
            literal_to_hyperedges.clear();
            literal_to_removed.clear();
            literal_iso_inv.clear();
            clause_tombstone.clear();

            literal_to_binary_clauses.shrink_to_fit();
            literal_to_ternary_clauses.shrink_to_fit();
            literal_to_hyperedges.shrink_to_fit();
            literal_to_removed.shrink_to_fit();
            literal_iso_inv.shrink_to_fit();
            clause_tombstone.shrink_to_fit();
        }
    };
}

#endif //SATSUMA_HYPERGRAPH_H
