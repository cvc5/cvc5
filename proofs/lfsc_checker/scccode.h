#ifndef SCC_CODE_H
#define SCC_CODE_H

#include "check.h"

void init_compiled_scc();

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args );

inline Expr* f_append( Expr* c1, Expr* c2 );

inline Expr* f_simplify_clause( Expr* c );

inline Expr* f_mpz_sub( Expr* x, Expr* y );

inline Expr* f_mp_ispos( Expr* x );

inline Expr* f_mpz_eq( Expr* x, Expr* y );

inline Expr* f_mpz_lt( Expr* x, Expr* y );

inline Expr* f_mpz_lte( Expr* x, Expr* y );

inline Expr* f_mpz_( Expr* x, Expr* y );

inline Expr* f_bblt_len( Expr* v );

inline Expr* f_bblast_const( Expr* v, Expr* n );

inline Expr* f_bblast_var( Expr* x, Expr* n );

inline Expr* f_bblast_concat( Expr* x, Expr* y );

inline Expr* f_bblast_extract_rec( Expr* x, Expr* i, Expr* j, Expr* n );

inline Expr* f_bblast_extract( Expr* x, Expr* i, Expr* j, Expr* n );

inline Expr* f_extend_rec( Expr* x, Expr* i, Expr* b );

inline Expr* f_bblast_zextend( Expr* x, Expr* i );

inline Expr* f_bblast_sextend( Expr* x, Expr* i );

inline Expr* f_bblast_bvand( Expr* x, Expr* y );

inline Expr* f_bblast_bvnot( Expr* x );

inline Expr* f_bblast_bvor( Expr* x, Expr* y );

inline Expr* f_bblast_bvxor( Expr* x, Expr* y );

inline Expr* f_bblast_bvadd_carry( Expr* a, Expr* b, Expr* carry );

inline Expr* f_bblast_bvadd( Expr* a, Expr* b, Expr* carry );

inline Expr* f_bblast_zero( Expr* n );

inline Expr* f_bblast_bvneg( Expr* x, Expr* n );

inline Expr* f_reverse_help( Expr* x, Expr* acc );

inline Expr* f_reverseb( Expr* x );

inline Expr* f_top_k_bits( Expr* a, Expr* k );

inline Expr* f_bottom_k_bits( Expr* a, Expr* k );

inline Expr* f_k_bit( Expr* a, Expr* k );

inline Expr* f_and_with_bit( Expr* a, Expr* bt );

inline Expr* f_mult_step_k_h( Expr* a, Expr* b, Expr* res, Expr* carry, Expr* k );

inline Expr* f_mult_step( Expr* a, Expr* b, Expr* res, Expr* n, Expr* k );

inline Expr* f_bblast_bvmul( Expr* a, Expr* b, Expr* n );

inline Expr* f_bblast_eq_rec( Expr* x, Expr* y, Expr* f );

inline Expr* f_bblast_eq( Expr* x, Expr* y );

inline Expr* f_bblast_bvult( Expr* x, Expr* y, Expr* n );

inline Expr* f_bblast_bvslt( Expr* x, Expr* y, Expr* n );

inline Expr* f_mk_ones( Expr* n );

inline Expr* f_mk_zero( Expr* n );

#endif

