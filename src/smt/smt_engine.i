%{
#include "smt/smt_engine.h"
%}

#ifdef SWIGJAVA

%typemap(javacode) CVC4::SmtEngine %{
  // a ref is kept here to keep Java GC from collecting the EM
  // before the SmtEngine
  private ExprManager em;
%}

%typemap(javaconstruct) SmtEngine {
  this($imcall, true);
  this.em = em; // keep ref to expr manager in SWIG proxy class
}

%typemap(javaout) CVC4::Expr {
  return new Expr(this.em, $jnicall, true);
}

%typemap(javaout) CVC4::UnsatCore {
  return new UnsatCore(this.em, $jnicall, true);
}

// %template(Map_ExprExpr) std::map<CVC4::Expr, CVC4::Expr>;
%ignore CVC4::SmtEngine::getSynthSolutions(std::map<Expr, Expr>& sol_map);

#endif // SWIGJAVA

%ignore CVC4::SmtEngine::setLogic(const char*);
%ignore CVC4::SmtEngine::setReplayStream(ExprStream* exprStream);
%ignore CVC4::smt::currentProofManager();

%include "smt/smt_engine.h"
