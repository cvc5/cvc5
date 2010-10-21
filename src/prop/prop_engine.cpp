/*********************                                                        */
/*! \file prop_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway, dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the propositional engine of CVC4.
 **
 ** Implementation of the propositional engine of CVC4.
 **/

#include "cnf_stream.h"
#include "prop_engine.h"
#include "sat.h"

#include "theory/theory_engine.h"
#include "util/decision_engine.h"
#include "util/Assert.h"
#include "util/output.h"
#include "smt/options.h"
#include "util/result.h"

#include <utility>
#include <map>
#include <iomanip>

using namespace std;
using namespace CVC4::context;

namespace CVC4 {
namespace prop {

/** Keeps a boolean flag scoped */
class ScopedBool {

private:

  bool d_original;
  bool& d_reference;

public:

  ScopedBool(bool& reference) :
    d_reference(reference) {
    d_original = reference;
  }

  ~ScopedBool() {
    d_reference = d_original;
  }
};

PropEngine::PropEngine(DecisionEngine* de, TheoryEngine* te, 
                       Context* context, const Options& opts) :
  d_inCheckSat(false),
  // d_options(opts),
  d_decisionEngine(de),
  d_theoryEngine(te),
  d_context(context) {
  Debug("prop") << "Constructing the PropEngine" << endl;
  d_satSolver = new SatSolver(this, d_theoryEngine, d_context, opts);
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver);
  d_satSolver->setCnfStream(d_cnfStream);
}

PropEngine::~PropEngine() {
  Debug("prop") << "Destructing the PropEngine" << endl;
  delete d_cnfStream;
  delete d_satSolver;
}

void PropEngine::assertFormula(TNode node) {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as non-removable
  d_cnfStream->convertAndAssert(node, false, false);
}

void PropEngine::assertLemma(TNode node) {
  Assert(d_inCheckSat, "Sat solver should be in solve()!");
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as removable
  d_cnfStream->convertAndAssert(node, false, false);
}


void PropEngine::printSatisfyingAssignment(){
  const CnfStream::TranslationCache& transCache =
    d_cnfStream->getTranslationCache();
  Debug("prop-value") << "Literal | Value | Expr" << endl
                      << "----------------------------------------"
                      << "-----------------" << endl;
  for(CnfStream::TranslationCache::const_iterator i = transCache.begin(),
      end = transCache.end();
      i != end;
      ++i) {
    pair<Node, SatLiteral> curr = *i;
    SatLiteral l = curr.second;
    if(!sign(l)) {
      Node n = curr.first;
      SatLiteralValue value = d_satSolver->value(l);
      Debug("prop-value") << "'" << l << "' " << value << " " << n << endl;
    }
  }
}

Result PropEngine::checkSat() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "PropEngine::checkSat()" << endl;

  // Mark that we are in the checkSat
  ScopedBool scopedBool(d_inCheckSat);
  d_inCheckSat = true;

  // Check the problem
  bool result = d_satSolver->solve();

  if( result && Debug.isOn("prop") ) {
    printSatisfyingAssignment();
  }

  Debug("prop") << "PropEngine::checkSat() => "
                << (result ? "true" : "false") << endl;
  if(result && d_theoryEngine->isIncomplete()) {
    return Result(Result::SAT_UNKNOWN, Result::INCOMPLETE);
  }
  return Result(result ? Result::SAT : Result::UNSAT);
}

Node PropEngine::getValue(TNode node) {
  Assert(node.getKind() == kind::VARIABLE &&
         node.getType().isBoolean());
  SatLiteralValue v = d_satSolver->value(d_cnfStream->getLiteral(node));
  if(v == l_True) {
    return NodeManager::currentNM()->mkConst(true);
  } else if(v == l_False) {
    return NodeManager::currentNM()->mkConst(false);
  } else {
    Assert(v == l_Undef);
    return Node::null();
  }
}

void PropEngine::push() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "push()" << endl;
}

void PropEngine::pop() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "pop()" << endl;
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
