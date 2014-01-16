%{
#include "theory/logic_info.h"
%}

%ignore CVC4::LogicInfo::LogicInfo(const char*);

%rename(less) CVC4::LogicInfo::operator<(const LogicInfo&) const;
%rename(lessEqual) CVC4::LogicInfo::operator<=(const LogicInfo&) const;
%rename(greater) CVC4::LogicInfo::operator>(const LogicInfo&) const;
%rename(greaterEqual) CVC4::LogicInfo::operator>=(const LogicInfo&) const;

%rename(equals) CVC4::LogicInfo::operator==(const LogicInfo&) const;
%ignore CVC4::LogicInfo::operator!=(const LogicInfo&) const;

%ignore CVC4::operator<<(std::ostream&, const LogicInfo&);

%include "theory/logic_info.h"
