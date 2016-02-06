%{
#include "expr/emptyset.h"
%}

%rename(equals) CVC4::EmptySet::operator==(const EmptySet&) const;
%ignore CVC4::EmptySet::operator!=(const EmptySet&) const;

%rename(less) CVC4::EmptySet::operator<(const EmptySet&) const;
%rename(lessEqual) CVC4::EmptySet::operator<=(const EmptySet&) const;
%rename(greater) CVC4::EmptySet::operator>(const EmptySet&) const;
%rename(greaterEqual) CVC4::EmptySet::operator>=(const EmptySet&) const;

%rename(apply) CVC4::EmptySetHashFunction::operator()(const EmptySet&) const;

%ignore CVC4::operator<<(std::ostream& out, const EmptySet& es);

%include "expr/emptyset.h"
