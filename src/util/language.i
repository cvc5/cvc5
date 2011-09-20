%{
#include "util/language.h"
%}

%import "util/language.h"

%ignore CVC4::operator<<(std::ostream&, CVC4::language::input::Language);
%ignore CVC4::operator<<(std::ostream&, CVC4::language::output::Language);

%include "util/language.h"
