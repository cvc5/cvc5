%{
#include "util/exception.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Exception&);
%ignore CVC4::Exception::Exception(const char*);

%include "util/exception.h"
