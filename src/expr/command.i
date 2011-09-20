%{
#include "expr/command.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Command&);
%ignore CVC4::operator<<(std::ostream&, const Command*);
%ignore CVC4::operator<<(std::ostream&, BenchmarkStatus status);

%rename(beginConst) CVC4::CommandSequence::begin() const;
%rename(endConst) CVC4::CommandSequence::end() const;

%include "expr/command.h"
