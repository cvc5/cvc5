#include "mcsat/prop_engine.h"
#include "mcsat/solver.h"
#include "smt/smt_statistics_registry.h"
using namespace CVC4;
using namespace mcsat;

PropEngine::PropEngine(TheoryEngine* te, DecisionEngine* de, context::Context* sc, context::UserContext* uc,
                       std::ostream* replayLog, ExprStream* replayStream, LemmaChannels* channels)
: CVC4::prop::PropEngine(te, de, sc, uc, replayLog, replayStream, channels)
{
  d_mySC = new context::Context();
  d_myUC = new context::UserContext();

  d_solver = new Solver(d_myUC, d_mySC);
}

PropEngine::~PropEngine() {
  delete d_solver;
  delete d_myUC;
  delete d_mySC;
}

void PropEngine::assertFormula(TNode node) {
  d_solver->addAssertion(node, true);
}

void PropEngine::assertLemma(TNode node, bool negated, bool removable) {
  if (negated) {
    d_solver->addAssertion(node.notNode(), true);
  } else {
    d_solver->addAssertion(node, true);
  }
}

Result PropEngine::checkSat(unsigned long& millis, unsigned long& resource) {
  bool result = d_solver->check();
  if (result) return Result::SAT;
  else return Result::UNSAT;
}

void PropEngine::push() {
  // TODO
}

void PropEngine::pop() {
  // TODO
}
