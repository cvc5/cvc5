%{
#include "smt/logic_exception.h"
%}

%ignore CVC4::LogicException::LogicException(const char*);

%include "smt/logic_exception.h"
