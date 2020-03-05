%{
#include "expr/sequence.h"
%}

%rename(equals) CVC4::Sequence::operator==(const Sequence&) const;
%ignore CVC4::Sequence::operator!=(const Sequence&) const;

%rename(less) CVC4::Sequence::operator<(const Sequence&) const;
%rename(lessEqual) CVC4::Sequence::operator<=(const Sequence&) const;
%rename(greater) CVC4::Sequence::operator>(const Sequence&) const;
%rename(greaterEqual) CVC4::Sequence::operator>=(const Sequence&) const;

%rename(apply) CVC4::SequenceHashFunction::operator()(const Sequence&) const;

%ignore CVC4::operator<<(std::ostream& out, const Sequence& es);

%include "expr/sequence.h"
