#ifndef PRINT_SMT2_H
#define PRINT_SMT2_H

#define PRINT_SMT2

#include <iosfwd>

class Expr;

#ifdef PRINT_SMT2
void print_smt2( Expr* p, std::ostream& s, short mode = 0 );

bool is_smt2_poly_formula( Expr* p );
short get_mode( Expr* p );

#endif


#endif
