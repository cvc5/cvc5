%{
#include "util/sexpr.h"
%}

%ignore CVC4::operator<<(std::ostream&, const SExpr&);
%ignore CVC4::operator<<(std::ostream&, SExpr::SexprTypes);
%ignore CVC4::operator<<(std::ostream&, PrettySExprs);

// for Java and the like
%extend CVC4::SExpr {
  std::string toString() const { return self->getValue(); }
};/* CVC4::SExpr */

%ignore CVC4::SExpr::SExpr(int);
%ignore CVC4::SExpr::SExpr(unsigned int);
%ignore CVC4::SExpr::SExpr(unsigned long);
%ignore CVC4::SExpr::SExpr(const char*);

%rename(equals) CVC4::SExpr::operator==(const SExpr&) const;
%ignore CVC4::SExpr::operator!=(const SExpr&) const;

%include "util/sexpr.h"
