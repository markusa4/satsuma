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

#define PRINT_NO_NEWLINE(str) std::cout << str << std::flush;
#define PRINT(str) std::cout << str << std::endl;

/**
 * Used to make the output look a bit more structured.
 */
static void progress_print_split() {
    PRINT("\r______________________________________________________________");
}

/**
 * Prints heading of table in the output.
 */
static void progress_print_header() {
    progress_print_split();
    PRINT(std::setw(11) << std::left <<"T (ms)" << std::setw(11) << "delta(ms)" << std::setw(12) << "proc"
          << std::setw(16) << "p1"        << std::setw(16)        << "p2");
    progress_print_split();
}

int sat_to_graph(int l) {
    return 2*(abs(l)-1) + (l < 0);
}

int graph_to_sat(int vertex) {
    const bool is_neg = vertex % 2;
    int variable = floor(vertex/2) + 1;
    return variable * (is_neg?-1:1);
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
class timed_print {
    std::chrono::high_resolution_clock::time_point first;
    std::chrono::high_resolution_clock::time_point previous;
public:

    bool h_silent = false;

    timed_print() {
        first     = std::chrono::high_resolution_clock::now();
        previous  = first;
    }

    void print_header() const {
        if(h_silent) return;
        progress_print_header();
    }

    void print_split() const {
        if(h_silent) return;
        progress_print_split();
    }

    void print(const std::string& str) const {
        if(h_silent) return;
        PRINT("\r" << str);
    }

    void timer_print(const std::string& proc, const std::string& p1, const std::string& p2) {
        if(h_silent) return;
        auto now = std::chrono::high_resolution_clock::now();
        PRINT("\r" << std::fixed << std::setprecision(2) << std::setw(11) << std::left
                   << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - first).count()) / 1000000.0
                   << std::setw(11)
                   << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - previous).count()) / 1000000.0
                   << std::setw(12) << proc << std::setw(16) << p1 << std::setw(16) << p2);
        previous = now;
    }

    void timer_split() {
        previous = std::chrono::high_resolution_clock::now();
    }

    void timer_print(const std::string& proc, const int p1, const int p2) {
        if(h_silent) return;
        auto now = std::chrono::high_resolution_clock::now();
        PRINT("\r" << std::fixed << std::setprecision(2) << std::setw(11) << std::left
                   << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - first).count()) / 1000000.0
                   << std::setw(11)
                   << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - previous).count()) / 1000000.0
                   << std::setw(12) << proc << std::setw(16) << p1 << std::setw(16) << p2);
        previous = now;
    }

    void timer_print(const std::string& proc, const int p1, const double p2) {
        if(h_silent) return;
        auto now = std::chrono::high_resolution_clock::now();
        PRINT("\r" << std::fixed << std::setprecision(2) << std::setw(11) << std::left
                   << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - first).count()) / 1000000.0
                   << std::setw(11)
                   << (std::chrono::duration_cast<std::chrono::nanoseconds>(now - previous).count()) / 1000000.0
                   << std::setw(12) << proc << std::setw(16) << p1 << std::setw(16) << p2);
        previous = now;
    }

    void progress_current_method(const std::string& print) const  {
        if(h_silent) return;
        PRINT_NO_NEWLINE("\r>" << print);
    }
    void progress_current_method(const std::string& method_name, const std::string& var1, double var1_val,
                                        const std::string& var2, double var2_val) const  {
        if(h_silent) return;
        PRINT_NO_NEWLINE("\r>" << method_name << " " << var1 << "=" << var1_val << ", " << var2 << "=" << var2_val);
    }
    void progress_current_method(const std::string& method_name, const std::string& var1, int var1_val,
                                        const std::string& var2, int var2_val,
                                        const std::string& var3, double var3_val) const {
        if(h_silent) return;
        PRINT_NO_NEWLINE("\r>" << method_name << " "  << var1 << "=" << var1_val << ", " << var2 << "=" << var2_val
                               << ", " << var3 << "=" << var3_val);
    }

    void progress_current_method(const std::string& method_name, const std::string& var1, double var1_val,
                                        const std::string& var2, int var2_val,
                                        const std::string& var3, int var3_val,
                                        const std::string& var4, int var4_val) const  {
        if(h_silent) return;
        PRINT_NO_NEWLINE("\r>" << method_name << " "  << var1 << "=" << var1_val << ", " << var2 << "=" << var2_val
                               << ", " << var3 << "=" << var3_val << ", " << var4 << "=" << var4_val);
    }
};

#endif //SATSUMA_UTILITY_H
