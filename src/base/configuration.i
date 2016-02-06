%{
#include "base/configuration.h"
%}

%apply char **STRING_ARRAY { char const* const* }
%include "base/configuration.h"
%clear char const* const*;
