#ifndef SCC_CODE_H
#define SCC_CODE_H

#include <vector>

class Expr;

void init_compiled_scc();

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args );

#endif

