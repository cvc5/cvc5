%{
#include "util/result.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Result& r);

%rename(equals) CVC4::Result::operator==(const Result& r) const;
%ignore CVC4::Result::operator!=(const Result& r) const;

%ignore CVC4::operator<<(std::ostream&, enum Result::Sat);
%ignore CVC4::operator<<(std::ostream&, enum Result::Validity);
%ignore CVC4::operator<<(std::ostream&, enum Result::UnknownExplanation);

%include "util/result.h"
