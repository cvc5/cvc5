/*********************                                                        */
/*! \file prop_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the propositional engine of CVC4
 **
 ** Implementation of the propositional engine of CVC4.
 **/

#include "prop/prop_engine.h"

#include <iomanip>
#include <map>
#include <utility>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "decision/decision_engine.h"
#include "expr/expr.h"
#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "proof/proof_manager.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "prop/theory_proxy.h"
#include "smt/smt_statistics_registry.h"
#include "smt/command.h"
#include "theory/theory_engine.h"
#include "theory/theory_registrar.h"
#include "util/resource_manager.h"
#include "util/result.h"

using namespace std;
using namespace CVC4::context;


#ifdef CVC4_REPLAY
#  define CVC4_USE_REPLAY true
#else /* CVC4_REPLAY */
#  define CVC4_USE_REPLAY false
#endif /* CVC4_REPLAY */

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

PropEngine::PropEngine(TheoryEngine* te, DecisionEngine *de, Context* satContext,
                       Context* userContext, std::ostream* replayLog,
                       ExprStream* replayStream, LemmaChannels* channels) :
  d_inCheckSat(false),
  d_theoryEngine(te),
  d_decisionEngine(de),
  d_context(satContext),
  d_theoryProxy(NULL),
  d_satSolver(NULL),
  d_registrar(NULL),
  d_cnfStream(NULL),
  d_interrupted(false),
  d_resourceManager(NodeManager::currentResourceManager())
{

  Debug("prop") << "Constructing the PropEngine" << endl;

  d_satSolver = SatSolverFactory::createDPLLMinisat(smtStatisticsRegistry());

  d_registrar = new theory::TheoryRegistrar(d_theoryEngine);
  d_cnfStream = new CVC4::prop::TseitinCnfStream(
      d_satSolver, d_registrar, userContext, true);

  d_theoryProxy = new TheoryProxy(
      this, d_theoryEngine, d_decisionEngine, d_context, d_cnfStream, replayLog,
      replayStream, channels);
  d_satSolver->initialize(d_context, d_theoryProxy);

  d_decisionEngine->setSatSolver(d_satSolver);
  d_decisionEngine->setCnfStream(d_cnfStream);
  PROOF (
         ProofManager::currentPM()->initCnfProof(d_cnfStream, userContext);
         );
}

PropEngine::~PropEngine() {
  Debug("prop") << "Destructing the PropEngine" << endl;
  delete d_cnfStream;
  delete d_registrar;
  delete d_satSolver;
  delete d_theoryProxy;
}

void PropEngine::assertFormula(TNode node) {
  Assert(!d_inCheckSat, "Sat solver in solve()!");
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as non-removable
  d_cnfStream->convertAndAssert(node, false, false, RULE_GIVEN);
}

void PropEngine::assertLemma(TNode node, bool negated,
                             bool removable,
                             ProofRule rule,
                             TNode from) {
  //Assert(d_inCheckSat, "Sat solver should be in solve()!");
  Debug("prop::lemmas") << "assertLemma(" << node << ")" << endl;

  // Assert as (possibly) removable
  d_cnfStream->convertAndAssert(node, removable, negated, rule, from);
}

void PropEngine::requirePhase(TNode n, bool phase) {
  Debug("prop") << "requirePhase(" << n << ", " << phase << ")" << endl;

  Assert(n.getType().isBoolean());
  SatLiteral lit = d_cnfStream->getLiteral(n);
  d_satSolver->requirePhase(phase ? lit : ~lit);
}

bool PropEngine::isDecision(Node lit) const {
  Assert(isSatLiteral(lit));
  return d_satSolver->isDecision(d_cnfStream->getLiteral(lit).getSatVariable());
}

void PropEngine::printSatisfyingAssignment(){
  const CnfStream::NodeToLiteralMap& transCache =
    d_cnfStream->getTranslationCache();
  Debug("prop-value") << "Literal | Value | Expr" << endl
                      << "----------------------------------------"
                      << "-----------------" << endl;
  for(CnfStream::NodeToLiteralMap::const_iterator i = transCache.begin(),
      end = transCache.end();
      i != end;
      ++i) {
    pair<Node, SatLiteral> curr = *i;
    SatLiteral l = curr.second;
    if(!l.isNegated()) {
      Node n = curr.first;
      SatValue value = d_satSolver->modelValue(l);
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

  // TODO This currently ignores conflicts (a dangerous practice).
  d_theoryEngine->presolve();

  if(options::preprocessOnly()) {
    return Result(Result::SAT_UNKNOWN, Result::REQUIRES_FULL_CHECK);
  }

  // Reset the interrupted flag
  d_interrupted = false;

  // Check the problem
  SatValue result = d_satSolver->solve();

  if( result == SAT_VALUE_UNKNOWN ) {

    Result::UnknownExplanation why = Result::INTERRUPTED;
    if (d_resourceManager->outOfTime())
      why = Result::TIMEOUT;
    if (d_resourceManager->outOfResources())
      why = Result::RESOURCEOUT;

    return Result(Result::SAT_UNKNOWN, why);
  }

  if( result == SAT_VALUE_TRUE && Debug.isOn("prop") ) {
    printSatisfyingAssignment();
  }

  Debug("prop") << "PropEngine::checkSat() => " << result << endl;
  if(result == SAT_VALUE_TRUE && d_theoryEngine->isIncomplete()) {
    return Result(Result::SAT_UNKNOWN, Result::INCOMPLETE);
  }
  return Result(result == SAT_VALUE_TRUE ? Result::SAT : Result::UNSAT);
}

Node PropEngine::getValue(TNode node) const {
  Assert(node.getType().isBoolean());
  Assert(d_cnfStream->hasLiteral(node));

  SatLiteral lit = d_cnfStream->getLiteral(node);

  SatValue v = d_satSolver->value(lit);
  if(v == SAT_VALUE_TRUE) {
    return NodeManager::currentNM()->mkConst(true);
  } else if(v == SAT_VALUE_FALSE) {
    return NodeManager::currentNM()->mkConst(false);
  } else {
    Assert(v == SAT_VALUE_UNKNOWN);
    return Node::null();
  }
}

bool PropEngine::isSatLiteral(TNode node) const {
  return d_cnfStream->hasLiteral(node);
}

bool PropEngine::hasValue(TNode node, bool& value) const {
  Assert(node.getType().isBoolean());
  Assert(d_cnfStream->hasLiteral(node));

  SatLiteral lit = d_cnfStream->getLiteral(node);

  SatValue v = d_satSolver->value(lit);
  if(v == SAT_VALUE_TRUE) {
    value = true;
    return true;
  } else if(v == SAT_VALUE_FALSE) {
    value = false;
    return true;
  } else {
    Assert(v == SAT_VALUE_UNKNOWN);
    return false;
  }
}

void PropEngine::getBooleanVariables(std::vector<TNode>& outputVariables) const {
  d_cnfStream->getBooleanVariables(outputVariables);
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

void PropEngine::resetTrail()
{
  d_satSolver->resetTrail();
  Debug("prop") << "resetTrail()" << endl;
}

unsigned PropEngine::getAssertionLevel() const {
  return d_satSolver->getAssertionLevel();
}

bool PropEngine::isRunning() const {
  return d_inCheckSat;
}
void PropEngine::interrupt()
{
  if(! d_inCheckSat) {
    return;
  }

  d_interrupted = true;
  d_satSolver->interrupt();
  Debug("prop") << "interrupt()" << endl;
}

void PropEngine::spendResource(unsigned amount)
{
  d_resourceManager->spendResource(amount);
}

bool PropEngine::properExplanation(TNode node, TNode expl) const {
  if(! d_cnfStream->hasLiteral(node)) {
    Trace("properExplanation") << "properExplanation(): Failing because node "
                               << "being explained doesn't have a SAT literal ?!" << std::endl
                               << "properExplanation(): The node is: " << node << std::endl;
    return false;
  }

  SatLiteral nodeLit = d_cnfStream->getLiteral(node);

  for(TNode::kinded_iterator i = expl.begin(kind::AND),
        i_end = expl.end(kind::AND);
      i != i_end;
      ++i) {
    if(! d_cnfStream->hasLiteral(*i)) {
      Trace("properExplanation") << "properExplanation(): Failing because one of explanation "
                                 << "nodes doesn't have a SAT literal" << std::endl
                                 << "properExplanation(): The explanation node is: " << *i << std::endl;
      return false;
    }

    SatLiteral iLit = d_cnfStream->getLiteral(*i);

    if(iLit == nodeLit) {
      Trace("properExplanation") << "properExplanation(): Failing because the node" << std::endl
                                 << "properExplanation(): " << node << std::endl
                                 << "properExplanation(): cannot be made to explain itself!" << std::endl;
      return false;
    }

    if(! d_satSolver->properExplanation(nodeLit, iLit)) {
      Trace("properExplanation") << "properExplanation(): SAT solver told us that node" << std::endl
                                 << "properExplanation(): " << *i << std::endl
                                 << "properExplanation(): is not part of a proper explanation node for" << std::endl
                                 << "properExplanation(): " << node << std::endl
                                 << "properExplanation(): Perhaps it one of the two isn't assigned or the explanation" << std::endl
                                 << "properExplanation(): node wasn't propagated before the node being explained" << std::endl;
      return false;
    }
  }

  return true;
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
