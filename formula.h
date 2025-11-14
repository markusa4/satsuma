// Copyright 2025 Markus Anders
// This file is part of satsuma 1.2.
// See LICENSE for extended copyright information.

#ifndef SATSUMA_FORMULA_H
#define SATSUMA_FORMULA_H

#include "dejavu/groups.h"

class abstract_formula { 
    public:
    virtual bool is_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) { return false; };
    virtual bool complete_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) { return false; };
    virtual int n_variables() { return 0; };
    virtual int n_clauses() { return 0; };
};
#endif
