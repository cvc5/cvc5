%{
#include "expr/chain.h"
%}

%rename(equals) CVC4::Chain::operator==(const Chain&) const;
%ignore CVC4::Chain::operator!=(const Chain&) const;

%ignore CVC4::operator<<(std::ostream&, const Chain&);

%rename(apply) CVC4::ChainHashFunction::operator()(const CVC4::Chain&) const;

%include "expr/chain.h"
