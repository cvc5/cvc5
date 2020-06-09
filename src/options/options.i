%{
#include "options/options.h"
%}

%apply char** STRING_ARRAY { char* argv[] }
%include "options/options.h"
%clear char* argv[];
