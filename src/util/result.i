%{
#include "util/result.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Result& r);

%rename(equals) CVC4::Result::operator==(const Result& r) const;
%ignore CVC4::Result::operator!=(const Result& r) const;

%ignore CVC4::operator<<(std::ostream&, enum Result::Sat);
%ignore CVC4::operator<<(std::ostream&, enum Result::Validity);
%ignore CVC4::operator<<(std::ostream&, enum Result::UnknownExplanation);

%ignore CVC4::operator==(enum Result::Sat, const Result&);
%ignore CVC4::operator!=(enum Result::Sat, const Result&);

%ignore CVC4::operator==(enum Result::Validity, const Result&);
%ignore CVC4::operator!=(enum Result::Validity, const Result&);

%include "util/result.h"
