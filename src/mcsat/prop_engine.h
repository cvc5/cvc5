#pragma once

#include "prop/prop_engine.h"

namespace CVC4 {
namespace mcsat {

class Solver;

class PropEngine : public CVC4::prop::PropEngine {

  /** The solver */
  Solver* d_solver;

  context::Context* d_mySC;
  context::UserContext* d_myUC;

  /** All assertions */
  std::vector<Node> d_assertions;

public:

  PropEngine(TheoryEngine*, DecisionEngine*, context::Context* satContext, context::UserContext* userContext);

  ~PropEngine();

  void assertFormula(TNode node);

  void assertLemma(TNode node, bool negated, bool removable);

  Result checkSat(unsigned long& millis, unsigned long& resource);

  virtual void push();

  virtual void pop();

};


}
}




