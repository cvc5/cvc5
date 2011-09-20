%{
#include "util/exception.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Exception&);

%include "util/exception.h"
