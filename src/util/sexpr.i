%{
#include "util/sexpr.h"
%}

%ignore CVC4::operator<<(std::ostream&, const SExpr&);
%ignore CVC4::operator<<(std::ostream&, SExpr::SexprTypes);

// for Java and the like
%extend CVC4::SExpr {
  std::string toString() const { return self->getValue(); }
};/* CVC4::SExpr */

%rename(equals) CVC4::SExpr::operator==(const SExpr&) const;
%ignore CVC4::SExpr::operator!=(const SExpr&) const;

%include "util/sexpr.h"
