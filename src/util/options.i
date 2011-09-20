%{
#include "util/options.h"
%}

%ignore CVC4::operator<<(std::ostream&, Options::SimplificationMode);
%ignore CVC4::operator<<(std::ostream&, Options::ArithPivotRule);

%import "util/exception.h"
%include "util/options.h"
