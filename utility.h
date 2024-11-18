// Copyright 2023 Markus Anders
// This file is part of dejavu 2.0.
// See LICENSE for extended copyright information.

#include <iostream>
#include <algorithm>
#include <random>
#include <unordered_map>
#include <unordered_set>
#include <fstream>
#include <set>
#include <cstring>
#include <queue>
#include <memory>
#include <chrono>
#include <iomanip>

#ifndef SATSUMA_UTILITY_H
#define SATSUMA_UTILITY_H

int sat_to_graph(int l) {
    return 2*(abs(l)-1) + (l < 0);
}

int graph_to_sat(int vertex) {
    const bool is_neg = vertex % 2;
    int variable = floor(vertex/2) + 1;
    return variable * (is_neg?-1:1);
}

int graph_negate(int vertex) {
    return sat_to_graph(-graph_to_sat(vertex));
}

void print_vector(std::vector<int>& vec) {
    for(auto v : vec) std::clog << v << " ";
    std::clog << std::endl;
}

class stopwatch {
    std::chrono::high_resolution_clock::time_point time_pt;
public:
    void start() {
        time_pt = std::chrono::high_resolution_clock::now();
    }

    double stop() {
        const std::chrono::high_resolution_clock::time_point now = std::chrono::high_resolution_clock::now();
        return (std::chrono::duration_cast<std::chrono::nanoseconds>(now - time_pt).count()) / 1000000.0;
    }
};

/**
 * \brief Prints information to the console.
 *
 * Contains additional facilities to measure elapsed time in-between prints.
 */
class profiler {
    std::vector<std::pair<std::string, double>> results;
public:
    void add_result(std::string name, double result) {
        results.push_back({name, result});
    }
    void print_results(std::ostream& print_to, const double independent_total = -1) {

        double total = 0;
        for (auto const &[name, time]: results) {
            total += time;
        }
        if(independent_total > 0 && independent_total > total) {
            const double t_other = independent_total - total;
            add_result("other", t_other);
            total = independent_total;
        }

        if(total == 0) total += 0.001;

        std::sort(results.begin(), results.end(), [](auto &left, auto &right) {
            return left.second > right.second;
        });

        print_to<< std::setprecision(2) << std::fixed;
        for(auto const& [name, time] : results) {
            print_to << "c " << std::right << std::setw(22) << time << "ms" << std::right << std::setw(6) << (time/total)*100 << std::setw(1) << "%"  << std::left << " " << name <<  "\n";
        }
        print_to << "c         ───────────────────────────────────────────────\n";
        print_to << "c " << std::right << std::setw(22) << total << "ms" << std::right << std::setw(6) << 100 << std::setw(1) << "%"  << std::left << " " << "total" <<  "\n";


    }
};

void terminate_with_error(std::string error_msg) {
    std::cerr << "c \nc " << error_msg << std::endl;
    exit(1);
}

[[maybe_unused]] static void print_automorphism(int n, const int *p, int nsupp, const int *supp) {
    static dejavu::markset test_set;
    test_set.initialize(n);
    test_set.reset();
    for(int i = 0; i < nsupp; ++i) {
        const int v_from = supp[i];
        if(test_set.get(v_from)) continue;
        int v_next = p[v_from];
        if(v_from == v_next) continue;
        test_set.set(v_from);
        std::clog << "(" << v_from;
        while(!test_set.get(v_next)) {
            test_set.set(v_next);
            std::clog << " " << v_next;
            v_next = p[v_next];
        }
        std::clog << ")";
    }
    std::clog << std::endl;
}

static int hash32shift(int key) {
    key = ~key + (key << 15); // key = (key << 15) - key - 1;
    key = key ^ (key >> 12);
    key = key + (key << 2);
    key = key ^ (key >> 4);
    key = key * 2057; // key = (key + (key << 3)) + (key << 11);
    key = key ^ (key >> 16);
    return key;
}


//static void hash_combine(size_t & seed, int const& v) {
//    seed ^= std::hash<int>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
//}

// Hash function
struct any_hash
{
    long operator()(const std::vector<int>
                    &myVector) const
    {
        long answer = myVector.size();

        for (int i : myVector)
        {
            answer ^= hash32shift(i) + 0x9e3779b9 +
                      (answer << 6) + (answer >> 2);
        }
        return answer;
    }
};

struct triple_hash {
    inline std::size_t operator()(const std::tuple<int,int,int> & v) const {
        return 48*get<0>(v)+24*hash32shift(get<1>(v))+hash32shift(get<2>(v));
    }
};

struct pair_hash {
    std::size_t operator()(const std::pair<int,int> & v) const {
        return v.first*31+hash32shift(v.second);
    }
};

#endif //SATSUMA_UTILITY_H
