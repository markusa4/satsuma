//
// Created by markus on 22.02.24.
//

#ifndef SATSUMA_GRAPH_TOOLS_H
#define SATSUMA_GRAPH_TOOLS_H

#include "dejavu/dejavu.h"

// perform edge flips according to quotient graph
void red_quotient_edge_flip(dejavu::sgraph *g, int *colmap, dejavu::markset& del_e, dejavu::worklist& wl) {
    if (g->v_size <= 1) return;

    del_e.reset();
    wl.reset(); // serves as the "test vector"

    dejavu::coloring c;
    g->initialize_coloring(&c, colmap);

    for (int y = 0; y < g->v_size; ++y) wl[y] = 0;

    for (int i = 0; i < g->v_size;) {
        int v = c.lab[i];
        for (int f = g->v[v]; f < g->v[v] + g->d[v]; ++f) {
            const int v_neigh = g->e[f];
            wl[c.vertex_to_col[v_neigh]] += 1;
        }

        for (int ii = 0; ii < c.ptn[i] + 1; ++ii) {
            const int vx = c.lab[i + ii];
            bool skipped_none = true;
            for (int f = g->v[vx]; f < g->v[vx] + g->d[vx]; ++f) {
                const int v_neigh = g->e[f];
                if (wl[c.vertex_to_col[v_neigh]] ==
                    c.ptn[c.vertex_to_col[v_neigh]] + 1) {
                    del_e.set(f); // mark edge for deletion (reverse edge is handled later automatically)
                    skipped_none = false;
                }
            }
            if(skipped_none) break;
        }

        for (int f = g->v[v]; f < g->v[v] + g->d[v]; ++f) {
            const int v_neigh = g->e[f];
            wl[c.vertex_to_col[v_neigh]] = 0;
        }

        i += c.ptn[i] + 1;
    }
}

// deletes vertices marked in 'del'
// assumes that g->v points to g->e in ascending order
void perform_del_edge(dejavu::sgraph *g, dejavu::markset& del_e) {
    if (g->v_size <= 1) return;

    std::vector<int> g_old_v;
    g_old_v.reserve(g->v_size);

    for (int i = 0; i < g->v_size; ++i) g_old_v.push_back(g->v[i]);

    // make graph smaller using the translation array
    int epos = 0;
    for (int i = 0; i < g->v_size; ++i) {
        const int old_v = i;
        const int new_v = old_v;

        if (new_v >= 0) {
            int new_d = 0;
            g->v[new_v] = epos;
            assert(g->v[new_v] <= g_old_v[new_v]);
            for (int j = g_old_v[old_v]; j < g_old_v[old_v] + g->d[old_v]; ++j) {
                const int ve = g->e[j];
                const int new_ve = ve;
                assert(j >= 0);
                assert(j < g->e_size);
                if (!del_e.get(j)) {
                    assert(new_ve >= 0);
                    ++new_d;
                    g->e[epos] = new_ve;
                    ++epos;
                }
            }

            g->d[new_v] = new_d;
        }
    }

    std::cout << g->e_size << "->" << epos << std::endl;
    g->e_size = epos;
}

#endif //SATSUMA_GRAPH_TOOLS_H
