%{
#include "util/bool.h"
%}

%rename(apply) CVC4::BoolHashFunction::operator()(bool) const;

%include "util/bool.h"
