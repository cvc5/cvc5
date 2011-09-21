%{
#include "util/options.h"
%}

%ignore CVC4::operator<<(std::ostream&, Options::SimplificationMode);
%ignore CVC4::operator<<(std::ostream&, Options::ArithPivotRule);

%include "util/options.h"
