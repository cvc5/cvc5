%{
#include "util/exception.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Exception&) throw();
%ignore CVC4::Exception::Exception(const char*) throw();

%include "util/exception.h"
