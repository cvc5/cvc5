%{
#include "expr/ascription_type.h"
%}

%rename(equals) CVC4::AscriptionType::operator==(const AscriptionType&) const;
%ignore CVC4::AscriptionType::operator!=(const AscriptionType&) const;

%rename(apply) CVC4::AscriptionTypeHashFunction::operator()(const AscriptionType&) const;

%ignore CVC4::operator<<(std::ostream&, AscriptionType);

%include "expr/ascription_type.h"
