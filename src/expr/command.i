%{
#include "expr/command.h"
%}

%ignore CVC4::operator<<(std::ostream&, const Command&) throw();
%ignore CVC4::operator<<(std::ostream&, const Command*) throw();
%ignore CVC4::operator<<(std::ostream&, BenchmarkStatus status) throw();

%ignore CVC4::GetProofCommand;

%rename(beginConst) CVC4::CommandSequence::begin() const throw();
%rename(endConst) CVC4::CommandSequence::end() const throw();

%include "expr/command.h"
