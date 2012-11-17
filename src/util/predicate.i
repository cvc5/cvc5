%{
#include "util/predicate.h"
%}

%rename(equals) CVC4::Predicate::operator==(const Predicate&) const;
%rename(toExpr) CVC4::Predicate::operator Expr() const;

%include "util/predicate.h"
