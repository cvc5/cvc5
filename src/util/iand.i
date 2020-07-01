%{
#include "util/iand.h"
%}

%rename(toUnsigned) CVC4::IntAnd::operator unsigned() const;

%ignore CVC4::operator<<(std::ostream&, const IntAnd&);

%include "util/iand.h"
