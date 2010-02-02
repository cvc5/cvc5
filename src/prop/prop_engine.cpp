/*********************                                           -*- C++ -*-  */
/** prop_engine.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
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
#include "prop/minisat/mtl/Vec.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "util/Assert.h"
#include "util/output.h"

#include <utility>
#include <map>

using namespace CVC4::prop::minisat;
using namespace std;

namespace CVC4 {

PropEngine::PropEngine(DecisionEngine& de, TheoryEngine& te) :
  d_de(de), 
  d_te(te){
  d_cnfStream = new CVC4::prop::TseitinCnfStream(this);
}

PropEngine::~PropEngine(){
  delete d_cnfStream;
}


void PropEngine::assertClause(vec<Lit> & c){
  /*we can also here add a context dependent queue of assertions
   *for restarting the sat solver
   */
  //TODO assert that each lit has been mapped to an atom or requested
  d_sat.addClause(c);
}

void PropEngine::registerAtom(const Node & n, Lit l){
  d_atom2lit.insert(make_pair(n,l));
  d_lit2atom.insert(make_pair(l,n));
}

Lit PropEngine::requestFreshLit(){
  Var v = d_sat.newVar();
  Lit l(v,false);
  return l;
}

void PropEngine::assertFormula(const Node& node) {
  d_cnfStream->convertAndAssert(node);
}

void PropEngine::solve() {

  //TODO: may need to restart if a previous query returned false

  d_sat.verbosity = 1;
  bool result = d_sat.solve();

  Notice() << "result is " << (result ? "sat/invalid" : "unsat/valid") << endl;
}

}/* CVC4 namespace */
