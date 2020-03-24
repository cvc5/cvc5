%{
#include "expr/expr_sequence.h"
%}

%rename(equals) CVC4::ExprSequence::operator==(const ExprSequence&) const;
%ignore CVC4::ExprSequence::operator!=(const ExprSequence&) const;
%ignore CVC4::ExprSequence::getSequence() const;

%rename(less) CVC4::ExprSequence::operator<(const ExprSequence&) const;
%rename(lessEqual) CVC4::ExprSequence::operator<=(const ExprSequence&) const;
%rename(greater) CVC4::ExprSequence::operator>(const ExprSequence&) const;
%rename(greaterEqual) CVC4::ExprSequence::operator>=(const ExprSequence&) const;

%rename(apply) CVC4::ExprSequenceHashFunction::operator()(const ExprSequence&) const;

%ignore CVC4::operator<<(std::ostream& out, const ExprSequence& es);

%include "expr/expr_sequence.h"
