%{
#include "options/options.h"
%}

%ignore CVC4::operator<<(std::ostream&, SimplificationMode);
%ignore CVC4::operator<<(std::ostream&, ArithPivotRule);

%apply char** STRING_ARRAY { char* argv[] }
%include "options/options.h"
%clear char* argv[];
