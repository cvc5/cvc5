%{
#include "smt/smt_engine.h"
%}

%ignore CVC4::SmtEngine::setLogic(const char*);
%ignore CVC4::SmtEngine::getProof;
%ignore CVC4::stats::getStatisticsRegistry(SmtEngine*);
%ignore CVC4::smt::beforeSearch(std::string, bool, SmtEngine*);

%include "smt/smt_engine.h"
