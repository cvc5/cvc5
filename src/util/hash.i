%{
#include "util/hash.h"
%}

%rename(apply) CVC4::StringHashFunction::operator()(const std::string&) const;

%include "util/hash.h"
