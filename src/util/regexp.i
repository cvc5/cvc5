%{
#include "util/regexp.h"
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

%rename(assign) CVC4::RegExp::operator=(const RegExp&);
%rename(equals) CVC4::RegExp::operator==(const RegExp&) const;
%ignore CVC4::RegExp::operator!=(const RegExp&) const;
%rename(less) CVC4::RegExp::operator<(const RegExp&) const;
%rename(lessEqual) CVC4::RegExp::operator<=(const RegExp&) const;
%rename(greater) CVC4::RegExp::operator>(const RegExp&) const;
%rename(greaterEqual) CVC4::RegExp::operator>=(const RegExp&) const;

%rename(apply) CVC4::strings::StringHashFunction::operator()(const ::CVC4::String&) const;
%rename(apply) CVC4::RegExpHashFunction::operator()(const RegExp&) const;

%ignore CVC4::operator<<(std::ostream&, const String&);
%ignore CVC4::operator<<(std::ostream&, const RegExp&);

%apply int &OUTPUT { int &c };
%include "util/regexp.h"
%clear int &c;
