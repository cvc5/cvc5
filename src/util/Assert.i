%{
#include "util/Assert.h"
%}

%rename(CVC4IllegalArgumentException) CVC4::IllegalArgumentException;
%ignore CVC4::InternalErrorException::InternalErrorException(const char*, const char*, unsigned, const char*, ...);

%include "util/Assert.h"
