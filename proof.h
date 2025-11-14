// Copyright 2025 Markus Anders, Wietze Koops
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_PROOF_H
#define SATSUMA_PROOF_H

#include "utility.h"
#include "dejavu/groups.h"
#include <boost/multiprecision/cpp_int.hpp>

class proof {
    enum order_type {NONE, SPARSE, DENSE};

    std::ostream& proof_file;
    long long constraints = 0;
    order_type loaded_order_type = NONE;
    long long loaded_order_size = 0;

    long long proof_dense_crossover = 0;

    //--------------------------------------------------------------------/
    // for dense proofs
    // 
    std::vector<std::string> lit_to_coefficient;
    long long to_delete_hint = -1;
    std::vector<int> delete_later;


    //--------------------------------------------------------------------/
    // for sparse proofs
    //
    // variable prefixes
    const char left         = 'u';            
    const char right        = 'v';
    const char auxs         = 'a';
    const char auxd         = 'd';
    const char fresh_right  = 'w';
    const char fresh_auxs_1 = 'b';
    const char fresh_auxd_1 = 'e';
    const char fresh_auxs_2 = 'c';
    const char fresh_auxd_2 = 'f';
    const char solver_auxs  = 's';
    const char solver_auxd  = 't';
    const char solvervar   = 'x';

    bool hinted = true;     // use hinted rup (unless it would blow up proof size)
    bool pol = true;        // use pol instead of rup as much as possible (unless it would blow up proof size)
    bool noproof1 = false;  // do not prove proofgoal #1 (replace with asserts)
    bool noproof2 = false;  // do not prove proofgoal #2 (replace with asserts)

    bool differentvars = true;
    long long nDominances = 0;
    
    bool hint_dvars = true;

    // counters for loaded order
    long long nauxvar = 0;
    long long nspec   = 0;
    long long ntrans  = 0;

    //std::vector<int> order;
    std::vector<int> lit_to_order_pos;

    //--------------------------------------------------------------------/
    // General helper procedures 
    //
    inline void add_count_constraints(long long add = 1) { 
        constraints += add;
    }

    inline long long count_constraint() { 
        return constraints;
    }

    void variable(long long literal) {
        proof_file << solvervar << abs(literal);
    }

    void literal(long long literal) {
        proof_file << (literal<0?"~":"") << solvervar << abs(literal);
    }

    void literal_prefix(char varname, long long idx, bool aux = false, bool neg = false) {
        if (idx < 0) {
            neg = !neg;
            idx = -idx;
        }
        if (neg) proof_file << "~";
        if (aux) proof_file << "$";
        proof_file << varname;
        if (differentvars && varname != solvervar && !aux) 
            proof_file << nDominances << "_";
        proof_file << idx << " ";
    }

    void literal_prefix_coefficient(char varname, long long idx, long long coeff, 
            bool aux = false, bool neg = false) {
        if (coeff == 0) return;
        if (coeff > 0) proof_file << "+";
        proof_file << coeff << " ";
        literal_prefix(varname, idx, aux, neg);
    }

    //--------------------------------------------------------------------/
    // Internal procedures for dense proofs 
    //
    void set_coefficient(long long lit, boost::multiprecision::cpp_int& coefficient) {
        lit_to_coefficient[sat_to_graph(lit)] = coefficient.str();
    }

    std::string get_coefficient(long long lit) {
        return lit_to_coefficient[sat_to_graph(lit)];
    }

    void lex_leader_dominance(const dejavu::groups::automorphism_workspace& sym, const std::vector<int>& support_order) {
        // dominance rule deriving the exponential encoding
        proof_file << "dom ";
        for(unsigned long long i = 0; i < support_order.size(); i++) {
            const long long  graph_lit = support_order[support_order.size() - i - 1]; // vars - i - 1
            const long long  lit       = graph_to_sat(graph_lit);
            const bool negated = lit < 0;

            auto map_lit = graph_to_sat(sym[graph_lit]);
            if(map_lit != lit)  {
                const bool map_negated = map_lit < 0;
                proof_file << "-" << get_coefficient(lit) << " " << (negated?"~":"")     << solvervar << abs(lit)     << " ";
                proof_file <<        get_coefficient(lit) << " " << (map_negated?"~":"") << solvervar << abs(map_lit) << " ";
            }
        }

        proof_file << " >= 0" << " : ";
        permutation(sym);
        proof_file << " :  subproof \nproofgoal #2\npol -1 -2 +;\nqed #2 : -1;\n";
        add_count_constraints(3);
        proof_file << "qed;\n";
        add_count_constraints();
        to_delete_hint = count_constraint();
    }

    void lex_leader_tseitin(const std::vector<int>& clause, const long long tseitin_var) {
        proof_file << "red ";
        for(auto l: clause){
            proof_file << "1 " << (l<0?"~":"");
            variable(l);
            proof_file << " ";
        }
        proof_file << " >= 1 : ";
        variable(tseitin_var);
        proof_file << " -> " << (tseitin_var>0?'1':'0') << ";\n";
        add_count_constraints();
    }

    void lex_leader_use_and_update_hint(const long long prev_lit) {
        proof_file << "pol " << to_delete_hint << " " << constraints << " " <<  get_coefficient(prev_lit) << " * " << " +;\n";
        constraints++;
        proof_file << "del id "<< to_delete_hint << ";\n";
        to_delete_hint = constraints;
    }

    void load_order_dense(std::vector<int>& order, long long domain_size) {
        lit_to_coefficient.resize(domain_size*2);

        // definition of pre-order
        long long order_id = count_constraint();
        proof_file << "def_order exp" << order_id << "\nvars\nleft ";
        unsigned long long variables = order.size();

        // left variables in pre-order definition
        for(unsigned long long i = 1; i <= variables; i++) proof_file << "u" << i << " ";

        // right variables in pre-order definition
        proof_file << ";\nright ";
        for(unsigned long long i = 1; i <= variables; i++) proof_file << "v" << i << " ";

        proof_file << ";\naux;\nend;\ndef\n";
        //proof_file << ";\naux\nend\ndef\n";

        // Note: quadratic runtime
        //unsigned long long coefficient = 1;
        boost::multiprecision::cpp_int coefficient = 1;

        for(unsigned long long i = 0; i < variables; i++) {
            const long long pos = variables - i;
            const long long lit = graph_to_sat(order[variables - i - 1]);
            const bool negated = lit < 0;
            set_coefficient(lit, coefficient);
            proof_file << " " << "-" << get_coefficient(lit) << " " << (negated?"~":"") <<  "u" << pos << " ";
            proof_file << ""  <<        get_coefficient(lit) << " " << (negated?"~":"") <<  "v" << pos;

            //if (coefficient > ULONG_MAX << 1) terminate_with_error("coefficient too large");
            //coefficient = coefficient << 1; // coefficient  * 2
            coefficient *= 2;
        }
        proof_file << ">= 0;\nend;\n";
        proof_file << "transitivity\nvars\nfresh_right";

        // fresh right variables to prove transitivity of pre-order
        for(unsigned long long i = 1; i <= variables; i++) proof_file << " w" << i;
        proof_file << ";\nend;\nproof\nproofgoal #1\n";
        proof_file << "pol 1 2 + 3 +;\nqed : -1;\nqed;\nend;\nend;\n";

        proof_file << "load_order exp" << order_id;
        for(const long long lit : order) {
            proof_file << " ";
            variable(graph_to_sat(lit));
        }
        proof_file << ";\n";
    }

    void sbp_dense(dejavu::groups::automorphism_workspace& automorphism,
            std::vector<int>& order_support, 
            long long tseitin_id_start,
            long long limit) {

        // apply dominance rule
        lex_leader_dominance(automorphism, order_support);

        long long extra_constraints = 0;
        int prev_lit = 0;
        int prev_sym = 0;
        int prev_tst = 0; 
        long long next_tseitin = tseitin_id_start;

        delete_later.clear();

        // construct the symmetry breaking clauses
        for (size_t i = 0; i < order_support.size(); ++i) {
            const int l   = graph_to_sat(order_support[i]);
            const int sym = graph_to_sat(automorphism.p()[sat_to_graph(l)]);
            int tst = 0;

            // reached depth limit
            if(static_cast<long long>(i) >= limit) break;

            if(extra_constraints == 0) {
                if(-l != sym)
                    rup_clause({-l, sym});
                else
                    rup_clause({-l});
            } else if(extra_constraints == 1) {
                tst = ++next_tseitin;
                lex_leader_tseitin({prev_sym, tst}, tst);       // (1)
                if(prev_sym != -prev_lit)
                    lex_leader_tseitin({-prev_lit,tst}, tst);       // (2)

                if(prev_sym != -prev_lit)
                    lex_leader_tseitin({-tst, -prev_sym, prev_lit}, -tst); // (5)
                else
                    lex_leader_tseitin({-tst, -prev_sym}, -tst); // (5)
                delete_later.push_back(count_constraint());

                lex_leader_use_and_update_hint(prev_lit);
                if(-l != sym)
                    rup_clause( {-tst, -l, sym});            // (3)
                else
                    rup_clause( {-tst, -l});            // (3)

                prev_tst = tst;
            } else {
                tst = ++next_tseitin;

                lex_leader_tseitin({prev_sym,  -prev_tst, tst}, tst);       // (1)
                if (prev_sym != -prev_lit)
                    lex_leader_tseitin({-prev_lit, -prev_tst, tst}, tst);       // (2)
                lex_leader_tseitin({-tst,       prev_tst},     -tst);       // (4)
                delete_later.push_back(count_constraint());

                if(prev_sym != -prev_lit)
                    lex_leader_tseitin({-tst, -prev_sym, prev_lit}, -tst); // (5)
                else
                    lex_leader_tseitin({-tst, -prev_sym}, -tst); // (5)
                delete_later.push_back(count_constraint());

                lex_leader_use_and_update_hint(prev_lit);
                if(-l != sym)
                    rup_clause( {-tst, -l, sym});            // (3)
                else
                    rup_clause( {-tst, -l});            // (3)
                prev_tst = tst;
            }

            ++extra_constraints;
            prev_lit = l;
            prev_sym = sym;
        }

        // delete unnecessary clauses -- necessary to remove them for optimization problems
        if(to_delete_hint != -1) delete_by_id(to_delete_hint);
        to_delete_hint = -1;
        for(auto constraint : delete_later) delete_by_id(constraint);
    }

    //--------------------------------------------------------------------/
    // Internal procedures for sparse proofs 
    //
    void unit_rup(char varname, long long idx, bool aux = false, 
            bool neg = false, long long hint = 0, long long extraHint = 0) {
        proof_file << "rup ";
        literal_prefix_coefficient(varname, idx, 1, aux, neg);
        proof_file << ">= 1";
        if (hint != 0) {
            proof_file << " : " << hint;
            if (extraHint != 0) proof_file << " " << extraHint;
        }
        proof_file << ";\n";
    }


    void binary_rup(char varname1, char varname2, long long idx1, long long idx2, 
            bool aux1, bool aux2, bool neg1, bool neg2) {
        proof_file << "rup ";
        literal_prefix_coefficient(varname1, idx1, 1, aux1, neg1);
        literal_prefix_coefficient(varname2, idx2, 1, aux2, neg2);
        proof_file << ">= 1;\n";
    }


    void ternary_rup(char varname1, char varname2, char varname3, 
            long long idx1, long long idx2, long long idx3,
            bool aux1, bool aux2, bool aux3, 
            bool neg1, bool neg2, bool neg3) {
        proof_file << "rup ";
        literal_prefix_coefficient(varname1, idx1, 1, aux1, neg1);
        literal_prefix_coefficient(varname2, idx2, 1, aux2, neg2);
        literal_prefix_coefficient(varname3, idx3, 1, aux3, neg3);
        proof_file << ">= 1;\n";
    }
    
    void vec_rup(char varname, std::vector<int> idxs, bool aux = false, bool neg = false) {
        proof_file << "rup ";
        for (auto idx: idxs)
            literal_prefix_coefficient(varname, idx, 1, aux, neg);
        proof_file << ">= " << idxs.size();
        proof_file << ";\n";
    }

    void variables_prefix(char varname, long long n, bool aux = false) {
        for (long long i = 1; i <= n; ++i) 
            literal_prefix(varname, i, aux);
    }

    void variables_specification() {
        proof_file << "vars" << "\n";
        proof_file << "left ";
        variables_prefix(left, loaded_order_size);
        proof_file << ";\n";
        proof_file << "right "; 
        variables_prefix(right, loaded_order_size);
        proof_file << ";\n";
        proof_file << "aux ";
        variables_prefix(auxs, nauxvar, true);
        variables_prefix(auxd, loaded_order_size, true);
        proof_file << ";\n";
        proof_file << "end vars;" << "\n";
    }

    void specification_s(char leftname, char rightname, char auxsname, 
            long long idx, long long idxl, long long idxr, bool auxiliary_vars,
            long long maxVarSolver = 0, long long limit = 0) {
        proof_file << "red ";
        bool negatel = idxl < 0;
        bool negater = idxr < 0;
        if (negatel) idxl = -idxl;
        if (negater) idxr = -idxr;
        char auxsname_idx = idx < limit ? solvervar : auxsname;
        long long auxs_idx = idx < limit ? maxVarSolver+idx : idx;   
        char auxsname_idxprev = idx-1 < limit ? solvervar : auxsname;
        long long auxs_idxprev = idx-1 < limit ? maxVarSolver+idx-1 : idx-1; 
        if (idx == 1) {
            literal_prefix_coefficient(auxsname_idx, auxs_idx, 
                    1, auxiliary_vars, true);    // ~a1
            literal_prefix_coefficient(leftname,  idxl, 1, false, negatel);          //  x1
            literal_prefix_coefficient(rightname, idxr, 1, false, not negater);      // ~y1
            proof_file << ">= 1 : ";
            literal_prefix(auxsname_idx, auxs_idx, auxiliary_vars);
            proof_file << "-> 0;\n";
        } else {
            literal_prefix_coefficient(auxsname_idx, auxs_idx,    
                    3, auxiliary_vars, true);  // 3 ~a_i
            literal_prefix_coefficient(auxsname_idxprev, auxs_idxprev, 
                    2, auxiliary_vars);        // 2 a_{i-1}
            literal_prefix_coefficient(leftname,  idxl,   1, false, negatel);        //  x_i
            literal_prefix_coefficient(rightname, idxr,   1, false, not negater);    // ~y_i
            proof_file << ">= 3 : ";
            literal_prefix(auxsname_idx, auxs_idx, auxiliary_vars);
            proof_file << "-> 0;\n";
        }
        proof_file << "red ";
        if (idx == 1) {
            literal_prefix_coefficient(auxsname_idx, auxs_idx,  
                    2, auxiliary_vars);          // 2 a1
            literal_prefix_coefficient(leftname,  idxl, 1, false, not negatel);      // ~x1
            literal_prefix_coefficient(rightname, idxr, 1, false, negater);          //  y1
            proof_file << ">= 2 : ";
            literal_prefix(auxsname_idx, auxs_idx, auxiliary_vars);
            proof_file << "-> 1;\n";
        } else {
            literal_prefix_coefficient(auxsname_idx, auxs_idx,   
                    2, auxiliary_vars);        // 2 a_i
            literal_prefix_coefficient(auxsname_idxprev, auxs_idxprev,  
                    2, auxiliary_vars, true);  // 2 ~a_{i-1}
            literal_prefix_coefficient(leftname,  idxl,   1, false, not negatel);    // ~x_i
            literal_prefix_coefficient(rightname, idxr,   1, false, negater);        // y_i
            proof_file << ">= 2 : ";
            literal_prefix(auxsname_idx, auxs_idx, auxiliary_vars);
            proof_file << "-> 1;\n";    
        }
    }


    void specification_d(char leftname, char rightname, char auxsname, 
            char auxdname, long long idx, long long idxl, long long idxr, bool auxiliary_vars,
            long long maxVarSolver = 0, long long limit = 0) {
        proof_file << "red ";
        bool negatel = idxl < 0;
        bool negater = idxr < 0;
        if (negatel) idxl = -idxl;
        if (negater) idxr = -idxr;
        char auxsname_idxprev = idx-1 < limit ? solvervar : auxsname;
        long long auxs_idxprev = idx-1 < limit ? maxVarSolver+idx-1 : idx-1; 
        if (idx == 1) {
            literal_prefix_coefficient(auxdname,  idx,  1, auxiliary_vars, true);    // ~d1
            literal_prefix_coefficient(leftname,  idxl, 1, false, not negatel);      // ~x1
            literal_prefix_coefficient(rightname, idxr, 1, false, negater);          //  y1

            proof_file << ">= 1 : ";
            literal_prefix(auxdname, 1, auxiliary_vars);
            proof_file << "-> 0;\n";
        } else {
            literal_prefix_coefficient(auxdname,  idx,   4, auxiliary_vars, true);   // 4 ~d_i
            literal_prefix_coefficient(auxdname,  idx-1, 3, auxiliary_vars);         // 3 d_{i-1}
        literal_prefix_coefficient(auxsname_idxprev, auxs_idxprev,   
                1, auxiliary_vars, true);   // ~a_{i-1}
        literal_prefix_coefficient(leftname,  idxl,  1, false, not negatel);     // ~x_i
        literal_prefix_coefficient(rightname, idxr,  1, false, negater);         // y_i
        proof_file << ">= 4 : ";
        literal_prefix(auxdname, idx, auxiliary_vars);
        proof_file << "-> 0;\n";
        }
        proof_file << "red ";
        if (idx == 1) {
            literal_prefix_coefficient(auxdname,  idx,  2, auxiliary_vars);         //  d1
            literal_prefix_coefficient(leftname,  idxl, 1, false, negatel);         //  x1
            literal_prefix_coefficient(rightname, idxr, 1, false, not negater);     // ~y1
            proof_file << ">= 2 : ";
            literal_prefix(auxdname, 1, auxiliary_vars);
            proof_file << "-> 1;\n";
        } else {
            literal_prefix_coefficient(auxdname,  idx,   3, auxiliary_vars);        // 3 d_i
            literal_prefix_coefficient(auxdname,  idx-1, 3, auxiliary_vars, true);  // 3 ~d_{i-1}
        literal_prefix_coefficient(auxsname_idxprev, auxs_idxprev,  
                1, auxiliary_vars);        // a_{i-1}
        literal_prefix_coefficient(leftname,  idxl,  1, false, negatel);        //  x_i
        literal_prefix_coefficient(rightname, idxr,  1, false, not negater);    // ~y_i
        proof_file << ">= 3 : ";
        literal_prefix(auxdname, idx, auxiliary_vars);
        proof_file << "-> 1;\n";
        }
    }

    void specification(char leftname, char rightname, char auxsname, char auxdname, bool write = false) {
        if (write) proof_file << "spec" << "\n";
        for (long long i = 1; i <= nauxvar; ++i) 
            specification_s(leftname, rightname, auxsname, i, i, i, true);
        for (long long i = 1; i <= loaded_order_size; ++i) 
            specification_d(leftname, rightname, auxsname, auxdname, i, i, i, true);
        if (write) proof_file<< "end spec;" << "\n";
    }
    
    void specification_for_sbp(char auxsname, char auxdname, std::vector<int> idxs, std::vector<int> perm,
            long long maxVarSolver, long long limit) {
        for (long long i = 1; i <= static_cast<long long>(idxs.size()) - 1; ++i) 
            specification_s(solvervar, solvervar, auxsname, i, idxs[i-1], perm[i-1], false, maxVarSolver, limit + 1);
        for (long long i = 1; i <= static_cast<long long>(idxs.size()); ++i) 
            specification_d(solvervar, solvervar, auxsname, auxdname, i, idxs[i-1], perm[i-1], false, maxVarSolver, limit + 1);
    }

    void definition() {
        proof_file << "def" << "\n";
        proof_file << "+1 ";
        literal_prefix(auxd, loaded_order_size, true);
        proof_file << ">= 1;" << "\n";
        proof_file << "end def;" << "\n";
    }

    void transitivity_variables() {
        proof_file << "vars" << "\n";
        proof_file << "fresh_right ";
        variables_prefix(fresh_right, loaded_order_size);
        proof_file << ";\n";
        proof_file << "fresh_aux_1 ";
        variables_prefix(fresh_auxs_1, nauxvar, true);
        variables_prefix(fresh_auxd_1, loaded_order_size, true);
        proof_file << ";\n";
        proof_file << "fresh_aux_2 ";
        variables_prefix(fresh_auxs_2, nauxvar, true);
        variables_prefix(fresh_auxd_2, loaded_order_size, true);
        proof_file << ";\n";
        proof_file << "end vars;" << "\n";
    }

    void transitivity_proof_unpack_all() {
        proof_file << "pol " << ntrans - 2;
        if (loaded_order_size > 1) proof_file << " 4 *"; 
        proof_file << " " << 4 * loaded_order_size - 3 << " +;\n";
        for (long long i = nauxvar; i > 0; --i) {
            unit_rup(auxd, i, true, false, hinted ? -1 : 0);
            proof_file << "pol -2 ";
            literal_prefix(auxd, i, true);
            proof_file << "w;\n";
            if (i > 1) proof_file << "pol -2 4 * " << 2 * loaded_order_size + 2 * i - 3 << " +;\n";
            else proof_file << "pol -2 " << 2 * loaded_order_size + 2 * i - 3 << " +;\n";
        }
        proof_file << "pol " << ntrans - 1;
        if (loaded_order_size > 1) proof_file << " 4 *"; 
        proof_file << " " << nspec + 4 * loaded_order_size - 3 << " +;\n";
        for (long long i = nauxvar; i > 0; --i) {
            unit_rup(fresh_auxd_1, i, true, false, hinted ? -1 : 0);
            proof_file << "pol -2 ";
            literal_prefix(fresh_auxd_1, i, true);
            proof_file << "w;\n";    
            if (i > 1) proof_file << "pol -2 4 * " << nspec + 2 * loaded_order_size + 2 * i - 3 << " +;\n";
            else proof_file << "pol -2 " << nspec + 2 * loaded_order_size + 2 * i - 3 << " +;\n";
        }
    }

    void transitivity_proof_lemmata() {
        if (loaded_order_size > 1) {
          proof_file << "pol 2 " << 2 * nspec + 1 << " + -1 + s;\n";
          proof_file << "pol " << nspec + 2 << " " 
              << 2 * nspec + 1 << " + " << ntrans + 3 * loaded_order_size - 2 << " + s;\n";
        }
        for (long long i = 2; i < loaded_order_size; ++i) {
            proof_file << "pol " << 2 * nspec + 2 * i - 1 << " ";
            literal_prefix(left, i);
            proof_file << "w ";
            literal_prefix(fresh_right, i);
            proof_file << "w s;\n";
            proof_file << "pol -1 -3 +;\n";
            proof_file << "pol -2 -3 +;\n";
            proof_file << "pol " << 2 * nspec + 2 * i - 1 << " ";
            literal_prefix(fresh_auxs_2, i - 1, true);
            proof_file << "w s;\n";
            proof_file << "pol -2 " << ntrans + 6 * loaded_order_size - 3 * i + 1
                << " + -1 + -3 2 * + " << 2 * i << " + s;\n";  
            proof_file << "pol -4 " << ntrans + 3 * loaded_order_size - 3 * i + 3 
                << " + -2 + -3 2 * + " << nspec + 2 * i << " + s;\n";  
        }
    }

    void transitivity_proof_derive() {
        long long startID = ntrans + 6 * loaded_order_size - 4;
        long long startD3 = 2 * nspec + 2 * nauxvar;
        proof_file << "pol " << ntrans + 3 * loaded_order_size - 2 << " " 
            << ntrans + 6 * loaded_order_size - 4 << " +;\n";
        proof_file << "pol -1 " << startD3 + 2 << " + s;\n";

        for (long long i = 2; i <= loaded_order_size; ++i) {
            proof_file << "pol " << ntrans + 3 * loaded_order_size + 3 - 3 * i << " " 
                << ntrans + 6 * loaded_order_size - 3 * i + 1 << " + " << startID + 6 * i - 11 << " + "
                << startID + 6 * i - 10 << " + s -1 3 * +;\n";
            proof_file << "pol -1 " << startD3 + 2 * i << " + s;\n";
        }
        proof_file << "pol -1 " << ntrans << " +;\n";
    }

    void transitivity() {
        proof_file << "transitivity\n";
        transitivity_variables();
        proof_file << "proof" << "\n";
        proof_file << "proofgoal #1" << "\n";
        transitivity_proof_unpack_all();
        transitivity_proof_lemmata();
        transitivity_proof_derive();
        proof_file << "qed #1 : -1;" << "\n";
        proof_file << "qed proof;" << "\n";
        proof_file << "end transitivity;\n";  
    }

    void reflexivity() {
        proof_file << "reflexivity\n";
        proof_file << "proof" << "\n";
        proof_file << "proofgoal #1" << "\n";
        proof_file << "rup >= 1;\n";  
        proof_file << "qed #1 : -1;" << "\n";
        proof_file << "qed proof;" << "\n";
        proof_file << "end reflexivity;\n";  
    }
    
    void pol_range(long long start, long long end) {
        proof_file << "pol " << start << " ";
        for (long long i = start+1; i < end; ++i) proof_file << i << " + ";
        proof_file << ";\n";
    }

    void recode_specification(const std::vector<int> &idxs, const std::vector<int> &perm, long long scopeStartID) {
        long long suppsize = idxs.size();
        long long scopeSpecDStartID = scopeStartID + 2*loaded_order_size - 2;

        // the constraints are a bit different for idx 1
        bool idxnot1 = (idxs[0] != 1);

        // recode all spec constraints to only the indexes in idxs
        // Note: these rup needs to be unhinted to avoid large printing time in solver
        unit_rup(auxd, idxs[suppsize-1], true, true);
        
        if (suppsize > 1) {
          if (idxnot1) {
              unit_rup(auxs, idxs[0]-1, true, false); 
              proof_file << "pol " << scopeStartID + 2*idxs[0] - 1 << " ";
              literal_prefix(auxs, idxs[0]-1, true, true);
              proof_file << "2 * + s;\n";
              proof_file << "pol " << scopeStartID + 2*idxs[0] << " -2 2 * +;\n";
          } else {
              proof_file << "rup >= 0;\n";
              proof_file << "pol " << scopeStartID + 1 << ";\n";
              proof_file << "pol " << scopeStartID + 2 << ";\n";
          }

          for (long long i = 1; i < suppsize-1; ++i) {
              binary_rup(auxs, auxs, idxs[i]-1, idxs[i-1], true, true, true, false);
              binary_rup(auxs, auxs, idxs[i]-1, idxs[i-1], true, true, false, true);
              proof_file << "pol " << scopeStartID + 2*idxs[i] - 1 << " -2 2 * +;\n";
              proof_file << "pol " << scopeStartID + 2*idxs[i] << " -2 2 * +;\n";
          }
          binary_rup(auxs, auxs, idxs[suppsize-1]-1, idxs[suppsize-2], true, true, true, false);
          binary_rup(auxs, auxs, idxs[suppsize-1]-1, idxs[suppsize-2], true, true, false, true);
        }

        if (idxnot1) {
            unit_rup(auxd, idxs[0]-1, true, false); 
            proof_file << "pol " << scopeSpecDStartID + 2*idxs[0] - 1 << " ";
            literal_prefix(auxd, idxs[0]-1, true, true);
            proof_file << "3 * + " << scopeStartID + 4 * loaded_order_size + 1 << " + s;\n";
            proof_file << "pol " << scopeSpecDStartID  + 2*idxs[0] << " -2 3 * + ";
            literal_prefix(auxs, idxs[0]-1, true, true);
            proof_file << "+;\n";
        } else {
            proof_file << "rup >= 0;\n";
            proof_file << "pol " << scopeSpecDStartID + 1 << ";\n";
            proof_file << "pol " << scopeSpecDStartID + 2 << ";\n";
        }

        for (long long i = 1; i < suppsize; ++i) {
            binary_rup(auxd, auxd, idxs[i]-1, idxs[i-1], true, true, true, false);
            binary_rup(auxd, auxd, idxs[i]-1, idxs[i-1], true, true, false, true);
            proof_file << "pol " << scopeSpecDStartID + 2*idxs[i] - 1 << " -2 3 * + " << -4*suppsize+2 << " + ;\n";
            proof_file << "pol " << scopeSpecDStartID + 2*idxs[i] << " -2 3 * + " << -4*suppsize << " + ;\n";
        }
    }
    
    void recode_specification_only_rups(const std::vector<int> &idxs, const std::vector<int> &perm, long long scopeStartID) {
        long long suppsize = idxs.size();

        // the constraints are a bit different for idx 1
        bool idxnot1 = (idxs[0] != 1);

        for (long long i = 1; i < suppsize; ++i) {
            binary_rup(auxs, auxs, idxs[i]-1, idxs[i-1], true, true, true, false); // proofgoalID  + i + 1 (used)
        }

        if (idxnot1) {
            unit_rup(auxd, idxs[0]-1, true, false);  // proofgoalID  + suppsize + 1 (used)
        } else {
            proof_file << "rup >= 0;\n";
        }

        for (long long i = 1; i < suppsize; ++i) {
            binary_rup(auxd, auxd, idxs[i]-1, idxs[i-1], true, true, false, true); // proofgoalID  + suppsize + i + 1 (used)
        }
    }

    void sbp_proofgoal1(const std::vector<int> &idxs, const std::vector<int> &perm, 
            const std::vector<int> &idxs_xvar, const std::vector<int> &perm_xvar,
            long long scopeStartID, long long maxVarSolver, long long limit) {
        long long suppsize = idxs.size();  
        
        if (noproof1) {
          for (long long i = 0; i < (15 * suppsize - 8  - pol * (8 * suppsize - 5)); ++i)
            proof_file << "a >= 1;\n";
        } else if (pol) {
            long long proofgoalID = scopeStartID + 4 * loaded_order_size - 1;
            long long scopeSpecDStartID = scopeStartID + 2*loaded_order_size - 2;
            long long maxID = scopeStartID - 4 * suppsize + 1;
            bool idxnot1 = (idxs[0] != 1);
            
            unit_rup(auxd, idxs[suppsize-1], true, true); // proofgoalID + 1
            recode_specification_only_rups(idxs, perm, scopeStartID);
            
            if (suppsize > 1) {
              proof_file << "pol " << maxID+1 << " " << scopeSpecDStartID + 2*idxs[0];
              if (idxnot1) {
                  proof_file << " " << proofgoalID  + suppsize + 1 << " 3 * + ";
                  literal_prefix(auxs, idxs[0]-1, true, true);
                  proof_file << "+";
              }
              proof_file << " + s " << proofgoalID  + suppsize + 2 << " +;\n";
            }
            for (long long i = 1; i < suppsize - 1; ++i) {
                proof_file << "pol " << maxID + 2*i+1 << " 3 * " 
                           << scopeSpecDStartID + 2*idxs[i] << " 2 * + -1 6 * + ";
                literal_prefix(solvervar, idxs_xvar[i]);
                proof_file << "w ";
                literal_prefix(solvervar, perm_xvar[i]);
                proof_file << "w ";
                literal_prefix(auxs, idxs[i]-1, true);
                proof_file << "w s " << proofgoalID + suppsize + i + 2 << " +;\n";
            }
            
            if (suppsize > 1) {
              proof_file << "pol " << scopeStartID + 2*idxs[0] - 1;
              if (idxnot1) {
                  proof_file << " ";
                  literal_prefix(auxs, idxs[0]-1, true, true);
                  proof_file << "2 * + ";
              }            
              proof_file << " " << maxID + 2*suppsize << " + s "
                         << proofgoalID  + 2 << " +;\n";
            }
            for (long long i = 1; i < suppsize - 1; ++i) {
                proof_file << "pol " << maxID + 2*suppsize + 2*i << " 2 * " 
                           << scopeStartID + 2*idxs[i] - 1 << " 3 * + -1 6 * + ";
                literal_prefix(solvervar, idxs_xvar[i]);
                proof_file << "w ";
                literal_prefix(solvervar, perm_xvar[i]);
                proof_file << "w ";
                literal_prefix(i-1 < limit ? solvervar : solver_auxs, i-1 < limit ? maxVarSolver+i : i);
                proof_file << "w s " << proofgoalID + i + 2 << " +;\n";
            }
            
            for (long long i = 0; i < suppsize - 1; ++i) {
                proof_file << "pol " << maxID + 2*suppsize + 2*i + 2 << " "
                           << -(2*suppsize-2) << " + ";
                literal_prefix(solvervar, idxs_xvar[i+1]);
                proof_file << "w ";
                literal_prefix(solvervar, perm_xvar[i+1]);
                proof_file << "w s;\n";
            }
            
            for (long long i = 0; i < suppsize - 1; ++i) {
                proof_file << "pol " << scopeSpecDStartID + 2*idxs[i+1] << " "
                           << -(2*suppsize-2) << " + ";
                literal_prefix(solvervar, idxs_xvar[i+1]);
                proof_file << "w ";
                literal_prefix(solvervar, perm_xvar[i+1]);
                proof_file << "w s;\n";
            }
            
            proof_file << "pol " << scopeSpecDStartID + 2*idxs[0];
            if (idxnot1) {
                proof_file << " " << proofgoalID  + suppsize + 1 << " 3 * + ";
                literal_prefix(auxs, idxs[0]-1, true, true);
                proof_file << "+";
            }
            proof_file << " " << maxID + 2 * suppsize << " + 3 d ";
            if (suppsize > 1) proof_file << proofgoalID  + suppsize + 2 << " +";
            proof_file << ";\n";
            for (long long i = 1; i < suppsize; ++i) {
                proof_file << "pol " << scopeSpecDStartID + 2*idxs[i] << " "
                           <<  maxID + 2 * suppsize + 2*i << " + "
                           << -suppsize << " -1 + s 3 * + "
                           << -2*suppsize+1 << " -1 + s 3 * + ";
                literal_prefix(auxs, idxs[i]-1, true);
                proof_file << "w ";  
                literal_prefix(i-1 < limit ? solvervar : solver_auxs, i-1 < limit ? maxVarSolver+i : i);
                proof_file << "w 6 d"; 
                if (i < suppsize-1) proof_file << " " << proofgoalID  + suppsize + i + 2 << " +";       
                proof_file << ";\n";  
            }
            
            proof_file << "pol " << proofgoalID+1 << " " << scopeStartID << " + -1 +;\n";
            
        } else {
            recode_specification(idxs, perm, scopeStartID);
          
            for (long long i = 0; i < suppsize - 1; ++i) {
                binary_rup(auxd, i < limit ? solvervar : solver_auxs, idxs[i], 
                        i < limit ? maxVarSolver+i+1 : i+1, true, false, false, true);
            }
            
            for (long long i = 0; i < suppsize - 1; ++i) {
                binary_rup(solver_auxd, auxs, i+1, idxs[i], false, true, false, true);
            }
            
            for (long long i = 0; i < suppsize - 1; ++i) {
                ternary_rup(solver_auxd, solver_auxd, auxd, i+2, i+1, idxs[i], 
                    false, false, true, false, true, false);
            }
            
            for (long long i = 0; i < suppsize - 1; ++i) {
                ternary_rup(auxd, auxd, solver_auxd, idxs[i+1], idxs[i], i+1, 
                    true, true, false, false, true, false);
            }
            
            for (long long i = 0; i < suppsize; ++i) {
              if (i > 0) {
                  binary_rup(auxd, solver_auxd, idxs[i-1], i+1, true, false, false, false);
                  binary_rup(auxd, solver_auxd, idxs[i], i, true, false, false, false);
              }
              binary_rup(auxd, solver_auxd, idxs[i], i+1, true, false, false, false);
            }
            
            proof_file << "rup >= 1;\n";
        }
        
    }

    void sbp_proofgoal2(const std::vector<int> &idxs, const std::vector<int> &perm, 
            long long scopeStartID, long long maxVarSolver, long long limit) {
        long long suppsize = idxs.size();  

        
        if (noproof2) {          
          for (long long i = 0; i < (3 * suppsize - 2 + pol * suppsize); ++i)
            proof_file << "a >= 1;\n";
        } else if (pol) {
          long long proofgoalID = scopeStartID + 4 * loaded_order_size - 1;
          long long maxID = scopeStartID - 4 * suppsize + 1 - (15 * suppsize + 4 * loaded_order_size - 9  - pol * (8 * suppsize - 5));
          long long domID = maxID + 4 * suppsize - 1;
          bool idxnot1 = (idxs[0] != 1);
          
          if (hint_dvars) {
              vec_rup(auxd, idxs, true);
              for (long long i = suppsize - 1; i >= 0; --i)
                  unit_rup(auxd, idxs[i], true, false, proofgoalID + 1);  // proofgoalID + suppsize - i
              proofgoalID += 1;
          } else {
              for (long long i = suppsize - 1; i >= 0; --i)
                  unit_rup(auxd, idxs[i], true);  // proofgoalID + suppsize - i
          }
          
          for (long long i = 1; i < suppsize; ++i) {
              binary_rup(auxs, auxs, idxs[i]-1, idxs[i-1], true, true, false, true); // proofgoalID + suppsize + i
          }
          
          if (idxnot1) {
              unit_rup(auxs, idxs[0]-1, true, false);   // proofgoalID + 2 * suppsize
          } else {
              proof_file << "rup >= 0;\n";
          }
          
          if (suppsize > 1) {
            proof_file << "pol " << scopeStartID + 2*idxs[0];
            if (idxnot1) {
                proof_file << " -1 2 * +";
            }
            proof_file << " " << maxID + 1 << " + 3 d;\n";
          }
          for (long long i = 1; i < suppsize - 1; ++i) {
              proof_file << "pol " << scopeStartID + 2*idxs[i] << " " 
                         << maxID + 2*i + 1 << " + -1 2 * + " << proofgoalID + suppsize + i  << " 2 * + 3 d;\n";
          }          
          
          if (idxnot1) {
              proof_file << "pol " << maxID + 2 * suppsize << " " 
                         << scopeStartID + 2 * loaded_order_size + 2*idxs[0] - 3 << " + " 
                         << proofgoalID + suppsize << " 4 * + ~$d" 
                         << idxs[0]-1 << " 3 * + "  
                         << proofgoalID + 2 * suppsize << " + 3 d;\n";
          } else {
              proof_file << "pol " << maxID + 2 * suppsize << " " 
                         << scopeStartID + 2 * loaded_order_size + 2*idxs[0] - 3 << " + " 
                         << proofgoalID + suppsize << " + s;\n";
          }
          for (long long i = 1; i < suppsize; ++i) {
              proof_file << "pol " << maxID + 2 * suppsize + 2*i << " " 
                         << scopeStartID + 2 * loaded_order_size + 2*idxs[i] - 3 << " + " 
                         << proofgoalID + suppsize - i << " 4 * + ~$d" 
                         << idxs[i]-1 << " 3 * + -1 3 * + "
                         << proofgoalID + suppsize + i << " + "
                         << proofgoalID + 2 * suppsize + i << " + 3 d;\n";
          }
          proof_file << "pol -1 " << domID << " +;\n";
            
        } else {
          for (long long i = suppsize - 2; i >= 0; --i) {
              unit_rup(auxd, idxs[i], true);
          }

          for (long long i = 0; i < suppsize - 1; ++i) {
              binary_rup(i < limit ? solvervar : solver_auxs, auxs, 
                      i < limit ? maxVarSolver+i+1 : i+1, idxs[i], false, true, true, false);
          }

          for (long long i = 0; i < suppsize - 1; ++i) {
              unit_rup(solver_auxd, i+1);
          }
          proof_file << "rup >= 1;\n";
      }

        
    }

    void recode_sbp(const std::vector<int> &idxs, const std::vector<int> &perm, long long maxID, long long limit) {
        long long suppsize = idxs.size();
        long long curMaxID = maxID + 22 * suppsize + 8 * loaded_order_size - 12 - pol * (7 * suppsize - 7) + (hint_dvars && pol);

        if (limit != suppsize - 1) {
          unit_rup(solver_auxd, limit+1);
          curMaxID += 1;
        }
           
        for (long long i = limit; i >= 1; --i) {
            if (hinted) unit_rup(solver_auxd, i, false, false, -1, maxID + 2 * suppsize + 2 * i - 1);
            else unit_rup(solver_auxd, i);
        }

        for (long long i = 0; i < limit; ++i) {
            proof_file << "pol " << maxID + 2*i + 2 << " ";
            literal_prefix(solvervar, idxs[i]);
            proof_file << "+ s;\n";
        }

        for (long long i = 0; i < limit; ++i) {
            proof_file << "pol " << maxID + 2*i + 2 << " "; 
            literal_prefix(solvervar, perm[i], false, true);
            proof_file << "+ s;\n";
        }

        proof_file << "pol " << maxID + 2*suppsize - 1 << " " << curMaxID + limit << " + s;\n";

        for (long long i = 2; i <= limit + 1; ++i) {
            proof_file << "pol " << maxID + 2*suppsize + 2*i-3 << " ";
            literal_prefix(solver_auxd, i-1, false, true);
            proof_file << "3 * + " << curMaxID + limit-i + 1 << " 4 * + s;\n";
        }
    }

    void load_order_sparse(std::vector<int>& order, long long domain_size) {
        // define order
        const long long order_id = count_constraint();
        nauxvar = loaded_order_size - 1;
        nspec   = 4 * loaded_order_size - 2;
        ntrans  = 3 * nspec + 3;
        proof_file << "def_order " << "lex" << order_id << "\n";
        variables_specification();
        specification(left, right, auxs, auxd, true);
        definition();
        transitivity();
        reflexivity();
        proof_file << "end def_order;\n";

        // load order
        proof_file << "load_order lex" << order_id;
        long long i = 0;
        for(const long long lit : order) {
            proof_file << " ";
            literal(graph_to_sat(lit));
            lit_to_order_pos[lit] = i + 1;
            ++i;
        }
        proof_file << ";\n";
    }

    void sbp_sparse(dejavu::groups::automorphism_workspace& automorphism,
            std::vector<int>& order_support, 
            long long tseitin_id_start,
            long long limit) {
        long long max_id = count_constraint();
        // log symmetry breaking constraints for the symmetry that maps variable x[idxs[i]] to x[perm[i]]
        long long suppsize = order_support.size();
        limit = std::min(suppsize - 1, limit - 1);

        // TODO rewrite methods to take automorphism/order_support instead
        std::vector<int> idxs;
        std::vector<int> perm;
        std::vector<int> idxs_varx;
        std::vector<int> perm_varx;
        for (long long i = 0; i < suppsize; ++i) {
            const long long lit_graph = order_support[i];
            const long long lit = graph_to_sat(lit_graph);
            const long long map = graph_to_sat(automorphism[lit_graph]);
            idxs.push_back(lit);
            perm.push_back(map);
            idxs_varx.push_back(lit > 0 ? lit : -lit);
            perm_varx.push_back(map > 0 ? map : -map);
        }

        // build the symmetry breaking circuit
        specification_for_sbp(solver_auxs, solver_auxd, idxs, perm, tseitin_id_start, limit);
        long long scopeStartID = max_id + 4 * suppsize - 1;

        proof_file << "dom ";
        literal_prefix_coefficient(solver_auxd, suppsize, 1);
        proof_file << " >= 1 : ";

        // witness
        for (long long i = 0; i < suppsize; ++i) {
            const long long lit = idxs[i];
            const long long map = perm[i];
            literal_prefix(solvervar, lit > 0 ? lit : -lit);
            literal_prefix(solvervar, lit > 0 ? map : -map);  
        }

        std::vector<int> proof_idxs;
        std::vector<int> proof_perm;
        for (long long i = 0; i < suppsize; ++i) {
            proof_idxs.push_back(lit_to_order_pos[sat_to_graph(idxs[i])]);
            proof_perm.push_back(lit_to_order_pos[sat_to_graph(perm[i])]);
        }

        proof_file << " : subproof\n";
        proof_file << "scope leq\n";
        proof_file << "proofgoal #1\n";
        sbp_proofgoal1(proof_idxs, proof_perm, idxs_varx, perm_varx, scopeStartID, tseitin_id_start, limit);
        proof_file << "qed #1 : -1;\n";
        proof_file << "end scope;\n";
        proof_file << "scope geq\n";
        proof_file << "proofgoal #2\n";
        scopeStartID += (15 * suppsize + 4 * loaded_order_size - 9  - pol * (8 * suppsize - 5));
        sbp_proofgoal2(proof_idxs, proof_perm, scopeStartID, tseitin_id_start, limit);
        proof_file << "qed #2 : -1;\n";
        proof_file << "end scope;\n";
        proof_file << "qed dom;\n";


        recode_sbp(idxs, perm, max_id, limit);

        // delete constraints that contain temporary variables
        proof_file << "del range " << max_id + 1 << " " << max_id +  4 * suppsize + 1 << ";\n";

        add_count_constraints(22 * suppsize + 8 * loaded_order_size - 12  - pol * (7 * suppsize - 7) + (hint_dvars && pol));
        max_id += 22 * suppsize + 8 * loaded_order_size - 12  - pol * (7 * suppsize - 7) + (hint_dvars && pol);

        // delete constraints used solely for SBP derivation, and the constraint added by dominance
        proof_file << "del range " << max_id << " " << max_id + limit + 1 + (limit != suppsize - 1) << ";\n";

        max_id +=  4 * limit + 1 + (limit != suppsize - 1);
        add_count_constraints(4 * limit + 1 + (limit != suppsize - 1));
        
        nDominances += 1;
    }

public:
    explicit proof(std::ostream& proof_file, const long long domain_size) : proof_file(proof_file) {
        lit_to_order_pos.resize(2*domain_size);
    };

    void set_proof_dense_crossover(long long crossover) {
        proof_dense_crossover = crossover;
    }

    void set_pol_logging(bool pol_logging) {
        pol = pol_logging;
    }

    void permutation(const dejavu::groups::automorphism_workspace& sym) {
        for(long long j = 0; j < sym.nsupp(); ++j) {
            const long long graph_lit = sym.supp()[j];
            const long long lit       = graph_to_sat(graph_lit);
            if(lit <= 0) continue;
            const long long map_lit = graph_to_sat(sym[graph_lit]);
            proof_file << " " ;

            // lit is positive, no need to check for negation
            variable(lit);
            proof_file << " -> ";
            literal(map_lit);
        }
    }

    void header(long long n_original_clauses) {
        constraints = n_original_clauses;
        proof_file << "pseudo-Boolean proof version 3.0\n";
        // proof_file << "f " << n_original_clauses << "\n";
    }

    void load_order(std::vector<int>& order, long long domain_size) {
        if(static_cast<long long>(order.size()) < proof_dense_crossover) {
            loaded_order_type = DENSE;
            loaded_order_size = order.size();
            load_order_dense(order, domain_size);
        } else {
            loaded_order_type = SPARSE;
            loaded_order_size = order.size();
            load_order_sparse(order, domain_size);
        }
    }

    void unload_order() {
        if(loaded_order_type != NONE) proof_file << "load_order;\n";
        loaded_order_type = NONE;
        loaded_order_size = 0;
    }

    void sbp(dejavu::groups::automorphism_workspace& automorphism,
            std::vector<int>& order_support, 
            long long tseitin_id_start,
            long long limit) {
        if(limit <= 0) return;
        if       (loaded_order_type == DENSE)  {
            sbp_dense(automorphism, order_support, tseitin_id_start + 1, limit);
        } else if(loaded_order_type == SPARSE) {
            sbp_sparse(automorphism, order_support, tseitin_id_start + 1, limit);
        }
    }

    void rup_clause(const std::vector<int>& clause){
        proof_file << "rup ";
        for(auto lit : clause){
            proof_file << "1 ";
            literal(lit);
            proof_file << " ";
        }
        proof_file << ">= 1;\n";
        add_count_constraints();
    }

    void drat_clause(const std::vector<int>& clause){
        proof_file << "red ";
        for(auto lit : clause){
            proof_file << "1 ";
            literal(lit);
            proof_file << " ";
        }
        proof_file << ">= 1 : ";

        if(clause.size() > 0) {
            const long long first_lit = clause[0];
            variable(first_lit);
            proof_file << " -> ";
            proof_file << (first_lit<0?"0":"1");
        }
        proof_file << ";\n";
        add_count_constraints();
    }

    void delete_by_id(const long long id) {
        proof_file << "del id " << id << ";\n";
    }


    void delete_clause(const long long id){
        proof_file << "delc " << id + 1 << ";\n";
    }
};

#endif //SATSUMA_PROOF_H
