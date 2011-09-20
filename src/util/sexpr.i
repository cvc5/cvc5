%{
#include "util/sexpr.h"
%}

%ignore CVC4::operator<<(std::ostream&, const SExpr&);

%include "util/sexpr.h"
