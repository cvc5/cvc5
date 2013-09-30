%{
#include "util/divisible.h"
%}

%rename(equals) CVC4::Divisible::operator==(const Divisible&) const;
%ignore CVC4::Divisible::operator!=(const Divisible&) const;

%ignore CVC4::operator<<(std::ostream&, const Divisible&);

%include "util/divisible.h"
