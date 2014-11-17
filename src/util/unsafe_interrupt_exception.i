%{
#include "util/unsafe_interrupt_exception.h"
%}

%ignore CVC4::UnsafeInterruptException::UnsafeInterruptException(const char*);

%include "util/unsafe_interrupt_exception.h"
