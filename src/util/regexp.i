%{
#include "util/regexp.h"
%}

%rename(equals) CVC4::RegExpRepeat::operator==(const RegExpRepeat&) const;

%rename(equals) CVC4::RegExpLoop::operator==(const RegExpLoop&) const;

%ignore CVC4::operator<<(std::ostream&, const RegExpRepeat&);
%ignore CVC4::operator<<(std::ostream&, const RegExpLoop&);

%include "util/regexp.h"
