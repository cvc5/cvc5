%{
#include "base/exception.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Exception&);
%ignore CVC4::Exception::Exception(const char*);
%typemap(javabase) CVC4::Exception "java.lang.RuntimeException";

// Make sure that the CVC4.Exception class of the Python API inherits from
// BaseException and can be caught
%exceptionclass CVC4::Exception;

%rename(CVC4IllegalArgumentException) CVC4::IllegalArgumentException;

%include "base/exception.h"
