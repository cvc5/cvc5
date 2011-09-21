%{
#include "smt/modal_exception.h"
%}

%ignore CVC4::ModalException::ModalException(const char*);

%include "smt/modal_exception.h"
