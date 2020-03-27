%{
#include "util/string.h"
%}

%rename(CVC4String) String;
%rename(CVC4StringHashFunction) CVC4::strings::StringHashFunction;

%ignore CVC4::String::String(const std::string&);

%rename(assign) CVC4::String::operator=(const String&);
%rename(getChar) CVC4::String::operator[](const unsigned int) const;
%rename(equals) CVC4::String::operator==(const String&) const;
%ignore CVC4::String::operator!=(const String&) const;
%rename(less) CVC4::String::operator<(const String&) const;
%rename(lessEqual) CVC4::String::operator<=(const String&) const;
%rename(greater) CVC4::String::operator>(const String&) const;
%rename(greaterEqual) CVC4::String::operator>=(const String&) const;

%rename(apply) CVC4::strings::StringHashFunction::operator()(const ::CVC4::String&) const;

%ignore CVC4::operator<<(std::ostream&, const String&);

%apply int &OUTPUT { int &c };
%include "util/string.h"
%clear int &c;
