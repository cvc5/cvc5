/*********************                                                        */
/** prop_engine.cpp
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "prop/prop_engine.h"
#include "prop/cnf_stream.h"

#include "theory/theory_engine.h"
#include "util/decision_engine.h"
#include "util/Assert.h"
#include "util/output.h"
#include "util/options.h"
#include "util/result.h"

#include <utility>
#include <map>

using namespace std;

namespace CVC4 {
namespace prop {

PropEngine::PropEngine(const Options* opts, DecisionEngine* de,
                       TheoryEngine* te) :
  d_opts(opts),
  d_de(de),
  d_te(te),
  d_restartMayBeNeeded(false) {
  d_sat = new SatSolver();
  d_cnfStream = new CVC4::prop::TseitinCnfStream(this);
}

PropEngine::~PropEngine() {
  delete d_cnfStream;
  delete d_sat;
}

void PropEngine::assertClause(SatClause& clause) {
  /*we can also here add a context dependent queue of assertions
   *for restarting the sat solver
   */
  //TODO assert that each lit has been mapped to an atom or requested
  d_sat->addClause(clause);
}

SatVariable PropEngine::registerAtom(const Node & n) {
  SatVariable v = requestFreshVar();
  d_atom2var.insert(make_pair(n, v));
  d_var2atom.insert(make_pair(v, n));
  return v;
}

SatVariable PropEngine::requestFreshVar() {
  return d_sat->newVar();
}

void PropEngine::assertFormula(const Node& node) {

  Debug("prop") << "Asserting ";
  node.printAst(Debug("prop"));
  Debug("prop") << endl;

  d_cnfStream->convertAndAssert(node);
  d_assertionList.push_back(node);
}

void PropEngine::restart() {
  delete d_sat;
  d_sat = new SatSolver();
  d_cnfStream->flushCache();
  d_atom2var.clear();
  d_var2atom.clear();

  for(vector<Node>::iterator iter = d_assertionList.begin(); iter
      != d_assertionList.end(); ++iter) {
    d_cnfStream->convertAndAssert(*iter);
  }
}

Result PropEngine::solve() {
  if(d_restartMayBeNeeded)
    restart();

  d_sat->verbosity = (d_opts->verbosity > 0) ? 1 : -1;
  bool result = d_sat->solve();

  if(!result) {
    d_restartMayBeNeeded = true;
  }

  Notice() << "result is " << (result ? "sat/invalid" : "unsat/valid") << endl;

  return Result(result ? Result::SAT : Result::UNSAT);
}

void PropEngine::assertLit(SatLiteral lit) {
  SatVariable var = literalToVariable(lit);
  if(isVarMapped(var)) {
    Node atom = lookupVar(var);
    //Theory* t = ...;
    //t must be the corresponding theory for the atom

    //Literal l(atom, sign(l));
    //t->assertLiteral(l );
  }
}

void PropEngine::signalBooleanPropHasEnded() {
}
//TODO decisionEngine should be told
//TODO theoryEngine to call lightweight theory propogation

}/* prop namespace */
}/* CVC4 namespace */
