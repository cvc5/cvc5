/*********************                                                        */
/** prop_engine.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "cnf_stream.h"
#include "prop_engine.h"
#include "sat.h"

#include "theory/theory_engine.h"
#include "util/decision_engine.h"
#include "util/Assert.h"
#include "util/output.h"
#include "util/options.h"
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

PropEngine::PropEngine(const Options* opts, DecisionEngine* de,
                       TheoryEngine* te, Context* context)
: d_inCheckSat(false),
  d_options(opts),
  d_decisionEngine(de),
  d_theoryEngine(te),
  d_context(context)
{
  Debug("prop") << "Constructing the PropEngine" << endl;
  d_satSolver = new SatSolver(this, d_theoryEngine, d_context, d_options);
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
  d_cnfStream->convertAndAssert(node);
}

void PropEngine::assertLemma(TNode node) {
  Assert(d_inCheckSat, "Sat solver should be in solve()!");
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as removable
  d_cnfStream->convertAndAssert(node);
}


void PropEngine::printSatisfyingAssignment(){
  const CnfStream::TranslationCache& transCache = d_cnfStream->getTranslationCache();
  Debug("prop-value") << "Literal | Value | Expr" << endl
                      << "---------------------------------------------------------" << endl;
  for(CnfStream::TranslationCache::const_iterator i = transCache.begin(),
      end = transCache.end();
      i != end;
      ++i) {
    pair<Node, SatLiteral> curr = *i;
    SatLiteral l = curr.second;
    if(!sign(l)) {
      Node n = curr.first;
      SatLiteralValue value = d_satSolver->value(l);
      Debug("prop-value") << /*setw(4) << */ "'" << l << "' " /*<< setw(4)*/ << value << " " << n
            << endl;
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

  if( result && debugTagIsOn("prop") ) {
    printSatisfyingAssignment();
  }

  Debug("prop") << "PropEngine::checkSat() => " << (result ? "true" : "false") << endl;
  return Result(result ? Result::SAT : Result::UNSAT);
}

void PropEngine::push() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "push()" << endl;
}

void PropEngine::pop() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "pop()" << endl;
}

}/* prop namespace */
}/* CVC4 namespace */
