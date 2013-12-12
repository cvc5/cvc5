#ifndef SCC_CODE_H
#define SCC_CODE_H

#include "check.h"

void init_compiled_scc();

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args );

inline Expr* f_litvar( Expr* l );

inline Expr* f_litpol( Expr* l );

inline Expr* f_notb( Expr* b );

inline Expr* f_iffb( Expr* b1, Expr* b2 );

inline Expr* f_clear_mark( Expr* v );

inline Expr* f_append( Expr* c1, Expr* c2 );

inline Expr* f_simplify_clause_h( Expr* pol, Expr* c );

inline Expr* f_simplify_clause( Expr* c );

#endif

