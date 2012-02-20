/*********************                                                        */
/*! \file prop_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): barrett, taking, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the propositional engine of CVC4
 **
 ** Implementation of the propositional engine of CVC4.
 **/

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat.h"

#include "theory/theory_engine.h"
#include "theory/registrar.h"
#include "util/Assert.h"
#include "util/options.h"
#include "util/output.h"
#include "util/result.h"
#include "expr/expr.h"
#include "expr/command.h"

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

PropEngine::PropEngine(TheoryEngine* te, Context* context) :
  d_inCheckSat(false),
  d_theoryEngine(te),
  d_context(context),
  d_satSolver(NULL),
  d_cnfStream(NULL),
  d_satTimer(*this),
  d_interrupted(false) {

  Debug("prop") << "Constructing the PropEngine" << endl;

  d_satSolver = new SatSolver(this, d_theoryEngine, d_context);

  theory::Registrar registrar(d_theoryEngine);
  d_cnfStream = new CVC4::prop::TseitinCnfStream(d_satSolver, registrar, Options::current()->threads > 1);

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
  d_cnfStream->convertAndAssert(d_theoryEngine->preprocess(node), false, false);
}

void PropEngine::assertLemma(TNode node, bool negated, bool removable) {
  //Assert(d_inCheckSat, "Sat solver should be in solve()!");
  Debug("prop::lemmas") << "assertLemma(" << node << ")" << endl;

  if(!d_inCheckSat && Dump.isOn("learned")) {
    Dump("learned") << AssertCommand(BoolExpr(node.toExpr())) << endl;
  } else if(Dump.isOn("lemmas")) {
    Dump("lemmas") << AssertCommand(BoolExpr(node.toExpr())) << endl;
  }

  //TODO This comment is now false
  // Assert as removable
  d_cnfStream->convertAndAssert(node, removable, negated);
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
    pair<Node, CnfStream::TranslationInfo> curr = *i;
    SatLiteral l = curr.second.literal;
    if(!sign(l)) {
      Node n = curr.first;
      SatLiteralValue value = d_satSolver->modelValue(l);
      Debug("prop-value") << "'" << l << "' " << value << " " << n << endl;
    }
  }
}

Result PropEngine::checkSat(unsigned long& millis, unsigned long& resource) {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "PropEngine::checkSat()" << endl;

  // Mark that we are in the checkSat
  ScopedBool scopedBool(d_inCheckSat);
  d_inCheckSat = true;

  // TODO This currently ignores conflicts (a dangerous practice).
  d_theoryEngine->presolve();

  if(Options::current()->preprocessOnly) {
    millis = resource = 0;
    return Result(Result::SAT_UNKNOWN, Result::REQUIRES_FULL_CHECK);
  }

  // Set the timer
  d_satTimer.set(millis);

  // Reset the interrupted flag
  d_interrupted = false;

  // Check the problem
  SatLiteralValue result = d_satSolver->solve(resource);

  millis = d_satTimer.elapsed();

  if( result == l_Undef ) {
    Result::UnknownExplanation why =
      d_satTimer.expired() ? Result::TIMEOUT :
        (d_interrupted ? Result::INTERRUPTED : Result::RESOURCEOUT);
    return Result(Result::SAT_UNKNOWN, why);
  }

  if( result == l_True && Debug.isOn("prop") ) {
    printSatisfyingAssignment();
  }

  Debug("prop") << "PropEngine::checkSat() => " << result << endl;
  if(result == l_True && d_theoryEngine->isIncomplete()) {
    return Result(Result::SAT_UNKNOWN, Result::INCOMPLETE);
  }
  return Result(result == l_True ? Result::SAT : Result::UNSAT);
}

Node PropEngine::getValue(TNode node) const {
  Assert(node.getType().isBoolean());
  Assert(d_cnfStream->hasLiteral(node));

  SatLiteral lit = d_cnfStream->getLiteral(node);

  SatLiteralValue v = d_satSolver->value(lit);
  if(v == l_True) {
    return NodeManager::currentNM()->mkConst(true);
  } else if(v == l_False) {
    return NodeManager::currentNM()->mkConst(false);
  } else {
    Assert(v == l_Undef);
    return Node::null();
  }
}

bool PropEngine::isSatLiteral(TNode node) const {
  return d_cnfStream->hasLiteral(node);
}

bool PropEngine::isTranslatedSatLiteral(TNode node) const {
  return d_cnfStream->isTranslated(node);
}

bool PropEngine::hasValue(TNode node, bool& value) const {
  Assert(node.getType().isBoolean());
  Assert(d_cnfStream->hasLiteral(node));

  SatLiteral lit = d_cnfStream->getLiteral(node);

  SatLiteralValue v = d_satSolver->value(lit);
  if(v == l_True) {
    value = true;
    return true;
  } else if(v == l_False) {
    value = false;
    return true;
  } else {
    Assert(v == l_Undef);
    return false;
  }
}

void PropEngine::ensureLiteral(TNode n) {
  d_cnfStream->ensureLiteral(n);
}

void PropEngine::push() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  d_satSolver->push();
  Debug("prop") << "push()" << endl;
}

void PropEngine::pop() {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  d_satSolver->pop();
  Debug("prop") << "pop()" << endl;
}

void PropEngine::interrupt() throw(ModalException) {
  if(! d_inCheckSat) {
    throw ModalException("SAT solver is not currently solving anything; "
                         "cannot interrupt it");
  }

  d_interrupted = true;
  d_satSolver->interrupt();
  Debug("prop") << "interrupt()" << endl;
}

void PropEngine::spendResource() throw() {
  // TODO implement me
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
