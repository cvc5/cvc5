%{
#include "smt/bad_option_exception.h"
%}

%ignore CVC4::BadOptionException::BadOptionException(const char*);

%include "smt/bad_option_exception.h"
