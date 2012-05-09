%{
#include "util/sexpr.h"
%}

%ignore CVC4::operator<<(std::ostream&, const SExpr&);
%ignore CVC4::operator<<(std::ostream&, SExpr::SexprTypes);

%include "util/sexpr.h"
