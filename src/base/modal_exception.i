%{
#include "base/modal_exception.h"
%}

%ignore CVC4::ModalException::ModalException(const char*);

%include "base/modal_exception.h"
