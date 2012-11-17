%{
#include "smt/smt_engine.h"
%}

%ignore CVC4::SmtEngine::getProof;
%ignore CVC4::stats::getStatisticsRegistry(SmtEngine*);

%include "smt/smt_engine.h"
