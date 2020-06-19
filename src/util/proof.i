%{
#include "util/proof.h"
%}

%ignore CVC4::Proof::toStream(std::ostream& out, const ProofLetMap& map) const;

%include "util/proof.h"
