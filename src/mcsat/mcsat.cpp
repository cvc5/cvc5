#include "mcsat/mcsat.h"
#include "mcsat/solver.h"
#include "smt/smt_engine_scope.h"

using namespace CVC4;
using namespace mcsat;

using namespace std;

MCSatEngine::MCSatEngine(ExprManager* em) throw()
: d_exprManager(em)
{
  d_smtEngine = new SmtEngine(em);
  smt::SmtScope scope(d_smtEngine);

  d_userContext = new context::UserContext();
  d_searchContext = new context::Context();
  d_mcSolver = new mcsat::Solver(d_userContext, d_searchContext);
}

MCSatEngine::~MCSatEngine() throw () {
  {
    smt::SmtScope scope(d_smtEngine);
    delete d_mcSolver;
    delete d_searchContext;
    delete d_userContext;
  }
  delete d_smtEngine;
}


void MCSatEngine::addAssertion(Expr assertion, bool process) {
  smt::SmtScope scope(d_smtEngine);
  d_mcSolver->addAssertion(assertion, process);
}

bool MCSatEngine::check() {
  smt::SmtScope scope(d_smtEngine);
  return d_mcSolver->check();
}

Statistics MCSatEngine::getStatistics() const throw() {
  return d_smtEngine->getStatistics();  
}
