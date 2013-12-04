%{
#include "util/subrange_bound.h"
%}

%rename(equals) CVC4::SubrangeBound::operator==(const SubrangeBound&) const;
%ignore CVC4::SubrangeBound::operator!=(const SubrangeBound&) const;
%rename(less) CVC4::SubrangeBound::operator<(const SubrangeBound&) const;
%rename(lessEqual) CVC4::SubrangeBound::operator<=(const SubrangeBound&) const;
%rename(greater) CVC4::SubrangeBound::operator>(const SubrangeBound&) const;
%rename(greaterEqual) CVC4::SubrangeBound::operator>=(const SubrangeBound&) const;

%rename(equals) CVC4::SubrangeBounds::operator==(const SubrangeBounds&) const;
%ignore CVC4::SubrangeBounds::operator!=(const SubrangeBounds&) const;
%rename(less) CVC4::SubrangeBounds::operator<(const SubrangeBounds&) const;
%rename(lessEqual) CVC4::SubrangeBounds::operator<=(const SubrangeBounds&) const;
%rename(greater) CVC4::SubrangeBounds::operator>(const SubrangeBounds&) const;
%rename(greaterEqual) CVC4::SubrangeBounds::operator>=(const SubrangeBounds&) const;

%rename(apply) CVC4::SubrangeBoundsHashFunction::operator()(const SubrangeBounds&) const;

%ignore CVC4::operator<<(std::ostream&, const SubrangeBound&);
%ignore CVC4::operator<<(std::ostream&, const SubrangeBounds&);

%include "util/subrange_bound.h"
