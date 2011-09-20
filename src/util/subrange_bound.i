%{
#include "util/subrange_bound.h"
%}

%rename(equals) CVC4::SubrangeBound::operator==(const SubrangeBound&) const;
%ignore CVC4::SubrangeBound::operator!=(const SubrangeBound&) const;

%ignore CVC4::operator<<(std::ostream&, const SubrangeBound&);

%include "util/subrange_bound.h"
