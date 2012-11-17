%{
#include "util/uninterpreted_constant.h"
%}

%rename(less) CVC4::UninterpretedConstant::operator<(const UninterpretedConstant&) const;
%rename(lessEqual) CVC4::UninterpretedConstant::operator<=(const UninterpretedConstant&) const;
%rename(greater) CVC4::UninterpretedConstant::operator>(const UninterpretedConstant&) const;
%rename(greaterEqual) CVC4::UninterpretedConstant::operator>=(const UninterpretedConstant&) const;

%rename(equals) CVC4::UninterpretedConstant::operator==(const UninterpretedConstant&) const;
%ignore CVC4::UninterpretedConstant::operator!=(const UninterpretedConstant&) const;

%include "util/uninterpreted_constant.h"
