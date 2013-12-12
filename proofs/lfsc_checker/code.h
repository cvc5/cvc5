#ifndef SC2_CODE_H
#define SC2_CODE_H

#include "expr.h"

Expr *read_code();
Expr *check_code(Expr *); // compute the type for the given code
Expr *run_code(Expr *); 

int read_index();

extern bool dbg_prog;
extern bool run_scc;

#endif 
