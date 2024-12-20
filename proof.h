// Copyright 2024 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PROOF_H
#define SATSUMA_PROOF_H

#include "utility.h"
#include <boost/multiprecision/cpp_int.hpp>

class proof_veripb {
  std::ostream& proof_file;
  int constraints = 0;
  std::vector<std::string> lit_to_coefficient;
  int to_delete_hint = -1;

  void log_variable(int literal) {
    proof_file << 'x' << abs(literal);
  }

  void set_coefficient(int lit, boost::multiprecision::cpp_int& coefficient) {
    lit_to_coefficient[sat_to_graph(lit)] = coefficient.str();
  }

  std::string get_coefficient(int lit) {
    return lit_to_coefficient[sat_to_graph(lit)];
  }

  void log_permutation(const dejavu::groups::automorphism_workspace& sym) {
    for(int j = 0; j < sym.nsupp(); ++j) {
      const int graph_lit = sym.supp()[j];
      const int lit = graph_to_sat(graph_lit);
      if(lit <= 0) continue;
      const int map_lit = graph_to_sat(sym[graph_lit]);
      proof_file << " " ;

      // lit is positive, no need to check for negation
      log_variable(lit);
      proof_file << " -> " << (map_lit<0?"~":"");
      log_variable(map_lit);
    }
  }

public:
  proof_veripb(std::ostream& proof_file) : proof_file(proof_file) {};

  void header(int n_original_clauses) {
    constraints = n_original_clauses;
    proof_file << "pseudo-Boolean proof version 1.2\n"
               << "f " << n_original_clauses << "\n";
  }

  void load_order_preamble(std::vector<int>& order, int domain_size) {
    lit_to_coefficient.resize(domain_size*2);

    // definition of pre-order
    int order_id = constraints;
    proof_file << "pre_order exp" << order_id << "\nvars\nleft ";
    unsigned int variables = order.size();

    // left variables in pre-order definition
    for(unsigned int i = 1; i <= variables; i++) proof_file << "u" << i << " ";

    // right variables in pre-order definition
    proof_file << "\nright ";
    for(unsigned int i = 1; i <= variables; i++) proof_file << "v" << i << " ";

    proof_file << "\naux\nend\ndef\n";

    // TODO this is quadratic runtime
    //auto  coefficient = mp::mpz_int(1);
    //auto  two = mp::mpz_int(2);

    //unsigned long long coefficient = 1;
    boost::multiprecision::cpp_int coefficient = 1;

    for(unsigned int i = 0; i < variables; i++) {
      const int pos = variables - i;
      const int lit = graph_to_sat(order[variables - i - 1]);
      const bool negated = lit < 0;
      set_coefficient(lit, coefficient);
      proof_file << "-" << get_coefficient(lit) << " " << (negated?"~":"") <<  "u" << pos << " ";
      proof_file << ""  << get_coefficient(lit) << " " << (negated?"~":"") <<  "v" << pos << " ";

      //if (coefficient > ULONG_MAX << 1) terminate_with_error("coefficient too large");
      //coefficient = coefficient << 1; // coefficient * 2
      coefficient *= 2;
    }
    proof_file << ">= 0;\nend\n";
    proof_file << "transitivity\nvars\nfresh_right ";

    // fresh right variables to prove transitivity of pre-order
    for(unsigned int i = 1; i <= variables; i++) proof_file << "w" << i << " ";
    proof_file << "\nend\nproof\nproofgoal #1" ;
    proof_file << "\np 1 2 + 3 +\nc -1\nqed\nqed\nend\nend\n";

    proof_file << "load_order exp" << order_id << " ";
    for(const int lit : order) {
      log_variable(graph_to_sat(lit));
      proof_file << " ";
    }
    proof_file << "\n";
  }

  void lex_leader_dominance(const dejavu::groups::automorphism_workspace& sym, const std::vector<int>& support_order) {
    // dominance rule deriving the exponential encoding
    proof_file << "dom ";
    for(unsigned int i = 0; i < support_order.size(); i++){
      const int  graph_lit = support_order[support_order.size() - i - 1]; // vars - i - 1
      const int  lit       = graph_to_sat(graph_lit);
      const bool negated = lit < 0;

      auto map_lit = graph_to_sat(sym[graph_lit]);
      if(map_lit != lit)  {
        const bool map_negated = map_lit < 0;
        proof_file << "-" << get_coefficient(lit) << " " << (negated?"~":"")     << "x" << abs(lit)     << " ";
        proof_file <<        get_coefficient(lit) << " " << (map_negated?"~":"") << "x" << abs(map_lit) << " ";
      }
    }

    proof_file << " >= 0" << " ; ";
    log_permutation(sym);
    proof_file << " ;  begin \nproofgoal #2\np -1 -2 +\nc -1\nqed\n";
    constraints += 3;
    proof_file << "qed\n";
    constraints++;
    to_delete_hint = constraints;
  }

  void lex_leader_clause(const std::vector<int>& clause){
    proof_file << "u ";
    for(auto lit : clause){
      proof_file << "1 " << (lit<0?"~":"");
      log_variable(lit);
      proof_file << " ";
    }

    proof_file << ">= 1 ;\n";
    //No idea why, but extra constraint seems to be used:
    ++constraints; //new constraint
  }

  void lex_leader_tseitin(const std::vector<int>& clause, const int tseitin_var) {
    proof_file << "red ";
    for(auto l: clause){
      proof_file << "1 " << (l<0?"~":"");
      log_variable(l);
      proof_file << " ";
    }
    proof_file << " >= 1 ; ";
    log_variable(tseitin_var);
    proof_file << " -> " << (tseitin_var>0?'1':'0') << '\n';
    constraints++;
  }

  void lex_leader_use_and_update_hint(const int prev_lit) {
    proof_file << "p " << to_delete_hint << " " << constraints << " " <<  get_coefficient(prev_lit) << " * " << " + \n";
    constraints++;
    proof_file << "d "<< to_delete_hint << "\n";
    to_delete_hint = constraints;
  }
};

#endif //SATSUMA_PROOF_H
