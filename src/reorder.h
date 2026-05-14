// Copyright 2026 Markus Anders
// This file is part of satsuma 1.4.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_REORDER_H
#define SATSUMA_REORDER_H

#include "formula.h"
#include "cnf.h"
#include "pbf.h"
#include "dejavu/ds.h"
#include <cstdint>

#pragma once

// cliquer
extern "C" {
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-compare"
#endif


#include "cliquer/cliquer.h"
#include "cliquer/graph.h"

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic pop
#endif
}

static void swap_columns(std::vector<std::vector<int>>& orbit_row, int j, int k) {
    // swap rows j and k
    for(size_t i = 0; i < orbit_row.size(); ++i) std::swap(orbit_row[i][j],orbit_row[i][k]);
}
static void swap_negation_behind(std::vector<std::vector<int>>& orbit_row, int j) {
    if(j+1 >= (int) orbit_row[0].size()) return;
    // find negation
    size_t i;
    for(i = 0; i < orbit_row[0].size(); ++i) {
        if(orbit_row[0][i] == graph_negate(orbit_row[0][j])) break;
    }
    if(i  >= orbit_row[0].size()) return;
    swap_columns(orbit_row, j+1, i);
}

static void reorder_columns_heuristic_weight(abstract_formula& formula, std::vector<std::vector<int>>& orbit_row) {
    dejavu::ds::workspace test_clauses(formula.n_clauses());

    int anchor_row         = -1;
    double anchor_row_clauses = -1;
    for(int i = 0; i < (int) orbit_row[0].size(); ++i) {
        const double in_clauses = formula.density(orbit_row[0][i]) / 1.0 * formula.in_clauses(orbit_row[0][i]);
        if(in_clauses > anchor_row_clauses) {
            anchor_row         = i;
            anchor_row_clauses = in_clauses;
        }
    }

    swap_columns(orbit_row, 0, anchor_row);
    swap_negation_behind(orbit_row, 0);
    formula.mark_clauses(test_clauses, orbit_row[0][0]);

    // selection sort
    for(int i = 2; i < (int) orbit_row[0].size(); i += 2) {
        int next_row         = i;
        int next_row_commons = 0;
        bool has_been_set = false;
        for(int j = i; j < (int) orbit_row[0].size(); ++j) {
            int in_clauses = formula.common_clauses(test_clauses, orbit_row[0][j]);
            if(in_clauses > next_row_commons) {
                has_been_set = true;
                next_row         = j;
                next_row_commons = in_clauses;
            } 
        }

        if(has_been_set) {
            swap_columns(orbit_row, i, next_row);
            swap_negation_behind(orbit_row, i);
            formula.mark_clauses(test_clauses, orbit_row[0][i]);
        } else break;
    }
}

static void reorder_columns_heuristic_clique(abstract_formula& formula, std::vector<std::vector<int>>& orbit_row) {
    dejavu::ds::markset   mark_variable(formula.n_variables());
    dejavu::ds::workspace var_to_vertex(2*formula.n_variables());
    dejavu::ds::workspace vertex_to_var(2*formula.n_variables());
    dejavu::ds::markset   in_row(2*formula.n_variables());
    dejavu::ds::workspace test_clauses(formula.n_clauses());

    int vertices = 0;
    // mark row
    for(int i = 0; i < (int) orbit_row[0].size(); ++i) {
        if(graph_to_sat(orbit_row[0][i]) < 0) continue;
        var_to_vertex[orbit_row[0][i]] =  vertices;
        vertex_to_var[vertices]        =  orbit_row[0][i];
        ++vertices;
        in_row.set(orbit_row[0][i]);
    }


    graph_t* cliquer_graph = graph_new(vertices);

    for(int i = 0; i < formula.n_clauses(); ++i) {
        for(int j = 0; j < formula.clause_size(i); ++j) {
            const int ll1 = formula.literal_at_clause_pos(i, j);
            const int v1  = sat_to_graph(ll1<0?-ll1:ll1);
            if(!in_row.get(v1)) continue;
            const int vertex1 = var_to_vertex[v1];
            for(int k = j+1; k < formula.clause_size(i); ++k) {
                const int ll2 = formula.literal_at_clause_pos(i, k);
                const int v2  = sat_to_graph(ll2<0?-ll2:ll2);
                if(!in_row.get(v2)) continue;
                const int vertex2 = var_to_vertex[v2];
                if(vertex1 != vertex2) GRAPH_ADD_EDGE(cliquer_graph, vertex1, vertex2);
            }
        }
    }

    // cliquer_options options;
    clique_options opts = *cliquer_default_options;
    opts.output  = NULL;            
    opts.time_function = NULL;
    opts.reorder_function = NULL;
    opts.reorder_map = NULL;
    //opts.user_function
    //
    //std::clog << "c \t [graph: #vertices " << vertices << " #edges " << graph_edge_count(cliquer_graph) 
    //           << "]" << std::endl;
    //std::clog << "c \t cliquer (no limit)" << std::endl; 
    set_t C = clique_unweighted_find_single(cliquer_graph, 0, 0, TRUE, &opts);
    in_row.reset();

    int clique_size = 0;
    if (C) {
        int v = -1;
        while ((v = set_return_next(C, v)) >= 0) {
            ++clique_size;
            in_row.set(vertex_to_var[v]);
        }
        set_free(C);       
    }

    graph_free(cliquer_graph);

    int actually_resorted = 0;
    // selection sort
    int i = 0;
    for(; i < (int) orbit_row[0].size(); i += 2) {
        bool has_been_set = false;
        int next_row         = i;
        for(int j = i; j < (int) orbit_row[0].size(); ++j) {
            if(in_row.get(orbit_row[0][j])) {
                next_row = j;
                has_been_set = true;
                break;
            }
        }

        if(has_been_set) {
            ++actually_resorted;
            swap_columns(orbit_row, i, next_row);
            swap_negation_behind(orbit_row, i);
            formula.mark_clauses(test_clauses, orbit_row[0][i]);
        } else break;
    }

    // sort rest by heuristic
    /*
    for(; i < (int) orbit_row[0].size(); i += 2) {
        int next_row         = i;
        int next_row_commons = 0;
        for(int j = i; j < (int) orbit_row[0].size(); ++j) {
            int in_clauses = formula.common_clauses(test_clauses, orbit_row[0][j]);
            if(in_clauses > next_row_commons) {
                next_row         = j;
                next_row_commons = in_clauses;
            } 
        }

        if(next_row != i) {
            swap_columns(orbit_row, i, next_row);
            swap_negation_behind(orbit_row, i);
            formula.mark_clauses(test_clauses, orbit_row[0][i]);
        } else break;
    }*/
}

static void reorder_columns(abstract_formula& formula, std::vector<std::vector<int>>& orbit_row, 
                            bool use_cliquer = true) {
    if(orbit_row.size() == 0) return;
    if(orbit_row[0].size() <= 4) return;
    if(orbit_row[0].size() <= 10000 && use_cliquer) reorder_columns_heuristic_clique(formula, orbit_row);
    else reorder_columns_heuristic_weight(formula, orbit_row);
}

#endif //SATSUMA_REORDER_H
