%{
#include "expr/uninterpreted_constant.h"
%}

%rename(less) CVC4::UninterpretedConstant::operator<(const UninterpretedConstant&) const;
%rename(lessEqual) CVC4::UninterpretedConstant::operator<=(const UninterpretedConstant&) const;
%rename(greater) CVC4::UninterpretedConstant::operator>(const UninterpretedConstant&) const;
%rename(greaterEqual) CVC4::UninterpretedConstant::operator>=(const UninterpretedConstant&) const;

%rename(equals) CVC4::UninterpretedConstant::operator==(const UninterpretedConstant&) const;
%ignore CVC4::UninterpretedConstant::operator!=(const UninterpretedConstant&) const;

%rename(apply) CVC4::UninterpretedConstantHashFunction::operator()(const UninterpretedConstant&) const;

%ignore CVC4::operator<<(std::ostream&, const UninterpretedConstant&);

%include "expr/uninterpreted_constant.h"
