%{
#include "util/pseudoboolean.h"
%}

%rename(toBool) CVC4::Pseudoboolean::operator bool() const;
%rename(toInt) CVC4::Pseudoboolean::operator int() const;
%rename(toInteger) CVC4::Pseudoboolean::operator Integer() const;

%ignore CVC4::operator<<(std::ostream&, CVC4::Pseudoboolean);

%include "util/pseudoboolean.h"
