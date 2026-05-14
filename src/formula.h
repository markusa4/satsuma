// Copyright 2026 Markus Anders
// This file is part of satsuma 1.3.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_FORMULA_H
#define SATSUMA_FORMULA_H

#include "dejavu/groups.h"

class abstract_formula { 
    public:
    virtual bool is_ulc(std::vector<int>& clause) { return false; };
    virtual bool is_amo(std::vector<int>& clause) { return false; };
    virtual bool is_clause(std::vector<int>& clause) { return false; };
    virtual int  in_clauses(int variable) { return 0; };
    virtual int  common_clauses(int variable1, int variable2) { return 0; };
    virtual int  density(int v) { return 0; };
    virtual int  common_clauses(dejavu::ds::workspace& test_clauses, int variable2) { return 0; };
    virtual int  common_clauses(dejavu::ds::markset& test_clauses, int variable2) { return 0; };
    virtual void mark_clauses(dejavu::ds::workspace& test_clauses1, int variable2) { };
    virtual void mark_clauses(dejavu::ds::markset& test_clauses1, int variable2) { };
    virtual void intersect_clauses(dejavu::ds::markset& test_clauses1, dejavu::ds::markset& test_clauses2, int variable2) { };
    virtual bool is_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) { return false; };
    virtual bool complete_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) { return false; };
    virtual int n_variables() { return 0; };
    virtual int n_clauses() { return 0; };
    virtual int literal_at_clause_pos(int clause, int pos) { return 0; };
    virtual int clause_size(int clause) { return 0; };
};
#endif
