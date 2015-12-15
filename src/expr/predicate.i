%{
#include "expr/predicate.h"
%}

%rename(equals) CVC4::Predicate::operator==(const Predicate&) const;
%rename(toExpr) CVC4::Predicate::operator Expr() const;

%rename(apply) CVC4::PredicateHashFunction::operator()(const Predicate&) const;

%ignore CVC4::operator<<(std::ostream&, const Predicate&);

%include "expr/predicate.h"
