%{
#include "util/output.h"
%}

%import "util/output.h"

%feature("valuewrapper") CVC4::null_streambuf;
%feature("valuewrapper") std::ostream;

%include "util/output.h"
