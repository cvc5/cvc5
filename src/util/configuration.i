%{
#include "util/configuration.h"
%}

%apply char **STRING_ARRAY { char const* const* }
%include "util/configuration.h"
%clear char const* const*;
