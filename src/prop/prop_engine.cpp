/*********************                                           -*- C++ -*-  */
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
#include "prop/minisat/mtl/Vec.h"
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "util/Assert.h"
#include "util/output.h"
#include "util/options.h"
#include "util/result.h"

#include <utility>
#include <map>

using namespace CVC4::prop::minisat;
using namespace std;

namespace CVC4 {

PropEngine::PropEngine(const Options* opts,
                       DecisionEngine& de,
                       TheoryEngine& te) :
  d_opts(opts),
  d_de(de), 
  d_te(te), 
  d_restartMayBeNeeded(false){
  d_sat = new Solver();
  d_cnfStream = new CVC4::prop::TseitinCnfStream(this);
}

PropEngine::~PropEngine(){
  delete d_cnfStream;
  delete d_sat;
}


void PropEngine::assertClause(vec<Lit> & c){
  /*we can also here add a context dependent queue of assertions
   *for restarting the sat solver
   */
  //TODO assert that each lit has been mapped to an atom or requested
  d_sat->addClause(c);
}

void PropEngine::registerAtom(const Node & n, Lit l){
  d_atom2lit.insert(make_pair(n,l));
  d_lit2atom.insert(make_pair(l,n));
}

Lit PropEngine::requestFreshLit(){
  Var v = d_sat->newVar();
  Lit l(v,false);
  return l;
}

void PropEngine::assertFormula(const Node& node) {

  Debug("prop") << "Asserting ";
  node.printAst(Debug("prop"));
  Debug("prop") << endl;

  d_cnfStream->convertAndAssert(node);
  d_assertionList.push_back(node);
}

void PropEngine::restart(){
  delete d_sat;
  d_sat = new Solver();
  d_cnfStream->flushCache();
  d_atom2lit.clear();
  d_lit2atom.clear();

  for(vector<Node>::iterator iter = d_assertionList.begin();
      iter != d_assertionList.end(); ++iter){
    d_cnfStream->convertAndAssert(*iter);
  }
}

static void printLit(ostream & out, Lit l) {
  const char * s = (sign(l))?"~":" ";
  out << s << var(l);

}

Result PropEngine::solve() {
  if(d_restartMayBeNeeded)
    restart();

  d_sat->verbosity = (d_opts->verbosity > 0) ? 1 : -1;
  bool result = d_sat->solve();

  if(!result){
    d_restartMayBeNeeded = true;
  }

  Notice() << "result is " << (result ? "sat/invalid" : "unsat/valid") << endl;
  
  if(result){
    for(map<Node,Lit>::iterator atomIter = d_atom2lit.begin();
	atomIter != d_atom2lit.end(); 
	++atomIter){
      Node n = (*atomIter).first;
      Lit l = (*atomIter).second;

      lbool lb = d_sat->modelValue(l);
      
      Notice() << n << "->" << lb.toInt() << endl;
    }
  }else{
    // unsat case
    Notice() << "Conflict {";
    for(int i=0; i< d_sat->conflict.size(); i++){
      Notice() << endl << " ";
      printLit(Notice(), d_sat->conflict[i]); 
    }
    Notice() << endl << "}" << endl;
  }

  return Result(result ? Result::SAT : Result::UNSAT);
}

}/* CVC4 namespace */
