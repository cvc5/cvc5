/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base for theory interface.
 */

#include "theory/theory.h"

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "theory/ee_setup_info.h"
#include "theory/ext_theory.h"
#include "theory/output_channel.h"
#include "theory/quantifiers_engine.h"
#include "theory/substitutions.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_rewriter.h"
#include "theory/theory_state.h"
#include "theory/trust_substitutions.h"

using namespace std;

namespace cvc5::internal {
namespace theory {

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::EFFORT_STANDARD:
    os << "EFFORT_STANDARD"; break;
  case Theory::EFFORT_FULL:
    os << "EFFORT_FULL"; break;
  case Theory::EFFORT_LAST_CALL:
    os << "EFFORT_LAST_CALL"; break;
  default:
      Unreachable();
  }
  return os;
}/* ostream& operator<<(ostream&, Theory::Effort) */

Theory::Theory(TheoryId id,
               Env& env,
               OutputChannel& out,
               Valuation valuation,
               std::string name)
    : EnvObj(env),
      d_instanceName(name),
      d_checkTime(statisticsRegistry().registerTimer(getStatsPrefix(id) + name
                                                     + "checkTime")),
      d_computeCareGraphTime(statisticsRegistry().registerTimer(
          getStatsPrefix(id) + name + "computeCareGraphTime")),
      d_sharedTerms(d_env.getContext()),
      d_out(&out),
      d_valuation(valuation),
      d_equalityEngine(nullptr),
      d_allocEqualityEngine(nullptr),
      d_theoryState(nullptr),
      d_inferManager(nullptr),
      d_quantEngine(nullptr),
      d_pnm(d_env.isTheoryProofProducing() ? d_env.getProofNodeManager()
                                           : nullptr),
      d_id(id),
      d_facts(d_env.getContext()),
      d_factsHead(d_env.getContext(), 0),
      d_sharedTermsIndex(d_env.getContext(), 0),
      d_careGraph(nullptr)
{
}

Theory::~Theory() {
}

bool Theory::needsEqualityEngine(EeSetupInfo& esi)
{
  // by default, this theory does not use an (official) equality engine
  return false;
}

void Theory::setEqualityEngine(eq::EqualityEngine* ee)
{
  // set the equality engine pointer
  d_equalityEngine = ee;
  if (d_theoryState != nullptr)
  {
    d_theoryState->setEqualityEngine(ee);
  }
  if (d_inferManager != nullptr)
  {
    d_inferManager->setEqualityEngine(ee);
  }
}

void Theory::setQuantifiersEngine(QuantifiersEngine* qe)
{
  // quantifiers engine may be null if not in quantified logic
  d_quantEngine = qe;
}

void Theory::setDecisionManager(DecisionManager* dm)
{
  Assert(dm != nullptr);
  if (d_inferManager != nullptr)
  {
    d_inferManager->setDecisionManager(dm);
  }
}

void Theory::finishInitStandalone()
{
  EeSetupInfo esi;
  if (needsEqualityEngine(esi))
  {
    // always associated with the same SAT context as the theory
    d_allocEqualityEngine =
        std::make_unique<eq::EqualityEngine>(d_env,
                                             context(),
                                             *esi.d_notify,
                                             esi.d_name,
                                             esi.d_constantsAreTriggers);
    // use it as the official equality engine
    setEqualityEngine(d_allocEqualityEngine.get());
  }
  finishInit();
}

TheoryId Theory::theoryOf(TNode node,
                          options::TheoryOfMode mode,
                          TheoryId usortOwner)
{
  TheoryId tid = THEORY_BUILTIN;
  switch(mode) {
    case options::TheoryOfMode::THEORY_OF_TYPE_BASED:
      // Constants, variables, 0-ary constructors
      if (node.isVar())
      {
        tid = theoryOf(node.getType(), usortOwner);
        if (theoryOf(node.getType(), usortOwner) == theory::THEORY_BOOL)
        {
          SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
          // Boolean variables belong to UF if they are "purify" variables.
          // Purify variables are considered theory literals and sent to the
          // UF theory to ensure theory combination is run properly on functions
          // having Boolean arguments.
          if (sm->getId(node) == SkolemFunId::PURIFY)
          {
            tid = THEORY_UF;
          }
        }
      }
      else if (node.getKind() == kind::EQUAL)
      {
        // Equality is owned by the theory that owns the domain
        tid = theoryOf(node[0].getType(), usortOwner);
      }
      else
      {
        // Regular nodes are owned by the kind. Notice that constants are a
        // special case here, where the theory of the kind of a constant
        // always coincides with the type of that constant.
        tid = kindToTheoryId(node.getKind());
      }
      break;
    case options::TheoryOfMode::THEORY_OF_TERM_BASED:
      // Variables
      if (node.isVar())
      {
        if (theoryOf(node.getType(), usortOwner) != theory::THEORY_BOOL)
        {
          // We treat the variables as uninterpreted
          tid = THEORY_UF;
        }
        else
        {
          SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
          if (sm->getId(node) == SkolemFunId::PURIFY)
          {
            // purify vars also go to UF
            tid = THEORY_UF;
          }
          else
          {
            // Other Boolean variables are Bool
            tid = THEORY_BOOL;
          }
        }
      }
      else if (node.getKind() == kind::EQUAL)
      {  // Equality
        TNode l = node[0];
        TNode r = node[1];
        TypeNode ltype = l.getType();
        TypeNode rtype = r.getType();
        // If the types are different, we must assign based on type due
        // to handling subtypes (limited to arithmetic). Also, if we are
        // a Boolean equality, we must assign THEORY_BOOL.
        if (ltype != rtype || ltype.isBoolean())
        {
          tid = theoryOf(ltype, usortOwner);
        }
        else
        {
          // If both sides belong to the same theory the choice is easy
          TheoryId T1 = theoryOf(l, mode, usortOwner);
          TheoryId T2 = theoryOf(r, mode, usortOwner);
          if (T1 == T2)
          {
            tid = T1;
          }
          else
          {
            TheoryId T3 = theoryOf(ltype, usortOwner);
            // This is a case of
            // * x*y = f(z) -> UF
            // * x = c      -> UF
            // * f(x) = read(a, y) -> either UF or ARRAY
            // at least one of the theories has to be parametric, i.e. theory
            // of the type is different from the theory of the term
            if (T1 == T3)
            {
              tid = T2;
            }
            else if (T2 == T3)
            {
              tid = T1;
            }
            else
            {
              // If both are parametric, we take the smaller one (arbitrary)
              tid = T1 < T2 ? T1 : T2;
            }
          }
        }
      }
      else
      {
        // Regular nodes are owned by the kind, which includes constants as a
        // special case.
        tid = kindToTheoryId(node.getKind());
      }
    break;
  default:
    Unreachable();
  }
  return tid;
}

void Theory::notifySharedTerm(TNode n)
{
  // do nothing
}

void Theory::notifyInConflict()
{
  if (d_inferManager != nullptr)
  {
    d_inferManager->notifyInConflict();
  }
}

void Theory::computeCareGraph() {
  Trace("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
        // If we know about it, we should have propagated it, so we can skip
        break;
      default:
        // Let's split on it
        addCarePair(a, b);
        break;
      }
    }
  }
}

void Theory::printFacts(std::ostream& os) const {
  unsigned i, n = d_facts.size();
  for(i = 0; i < n; i++){
    const Assertion& a_i = d_facts[i];
    Node assertion  = a_i;
    os << d_id << '[' << i << ']' << " " << assertion << endl;
  }
}

void Theory::debugPrintFacts() const{
  TraceChannel.getStream() << "Theory::debugPrintFacts()" << endl;
  printFacts(TraceChannel.getStream());
}

bool Theory::isLegalElimination(TNode x, TNode val)
{
  Assert(x.isVar());
  if (expr::hasSubterm(val, x))
  {
    return false;
  }
  if (val.getType() != x.getType())
  {
    return false;
  }
  if (!options().smt.produceModels || options().smt.modelVarElimUneval)
  {
    // Don't care about the model, or we allow variables to be eliminated by
    // unevaluatable terms, we can eliminate. Notice that when
    // options().smt.modelVarElimUneval is true, val may contain unevaluatable
    // kinds. This means that e.g. a Boolean variable may be eliminated based on
    // an equality (= b (forall ((x)) (P x))), where its model value is (forall
    // ((x)) (P x)).
    return true;
  }
  // If models are enabled, then it depends on whether the term contains any
  // unevaluable operators like FORALL, SINE, etc. Having such operators makes
  // model construction contain non-constant values for variables, which is
  // not ideal from a user perspective.
  // We also insist on this check since the term to eliminate should never
  // contain quantifiers, or else variable shadowing issues may arise.
  // there should be a model object
  TheoryModel* tm = d_valuation.getModel();
  Assert(tm != nullptr);
  return tm->isLegalElimination(x, val);
}

std::unordered_set<TNode> Theory::currentlySharedTerms() const
{
  std::unordered_set<TNode> currentlyShared;
  for (shared_terms_iterator i = shared_terms_begin(),
           i_end = shared_terms_end(); i != i_end; ++i) {
    currentlyShared.insert (*i);
  }
  return currentlyShared;
}

bool Theory::collectModelInfo(TheoryModel* m, const std::set<Node>& termSet)
{
  // if we are using an equality engine, assert it to the model
  if (d_equalityEngine != nullptr && !termSet.empty())
  {
    Trace("model-builder") << "Assert Equality engine for " << d_id
                           << std::endl;
    if (!m->assertEqualityEngine(d_equalityEngine, &termSet))
    {
      return false;
    }
  }
  Trace("model-builder") << "Collect Model values for " << d_id << std::endl;
  // now, collect theory-specific value assigments
  return collectModelValues(m, termSet);
}

void Theory::computeRelevantTerms(std::set<Node>& termSet)
{
  // by default, there are no additional relevant terms
}

void Theory::collectAssertedTerms(std::set<Node>& termSet,
                                  bool includeShared,
                                  const std::set<Kind>& irrKinds) const
{
  // Collect all terms appearing in assertions
  context::CDList<Assertion>::const_iterator assert_it = facts_begin(),
                                             assert_it_end = facts_end();
  for (; assert_it != assert_it_end; ++assert_it)
  {
    collectTerms(*assert_it, termSet, irrKinds);
  }

  if (includeShared)
  {
    // Add terms that are shared terms
    context::CDList<TNode>::const_iterator shared_it = shared_terms_begin(),
                                           shared_it_end = shared_terms_end();
    for (; shared_it != shared_it_end; ++shared_it)
    {
      collectTerms(*shared_it, termSet, irrKinds);
    }
  }
}
void Theory::collectAssertedTermsForModel(std::set<Node>& termSet,
                                          bool includeShared) const
{
  // use the irrelevant model kinds from the theory state
  const std::set<Kind>& irrKinds =
      d_theoryState->getModel()->getIrrelevantKinds();
  collectAssertedTerms(termSet, includeShared, irrKinds);
}

void Theory::collectTerms(TNode n,
                          std::set<Node>& termSet,
                          const std::set<Kind>& irrKinds) const
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (termSet.find(cur) != termSet.end())
    {
      // already visited
      continue;
    }
    Kind k = cur.getKind();
    // only add to term set if a relevant kind
    if (irrKinds.find(k) == irrKinds.end())
    {
      termSet.insert(cur);
    }
    // traverse owned terms, don't go under quantifiers
    if ((k == kind::NOT || k == kind::EQUAL || d_env.theoryOf(cur) == d_id)
        && !cur.isClosure())
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

bool Theory::collectModelValues(TheoryModel* m, const std::set<Node>& termSet)
{
  return true;
}

Theory::PPAssertStatus Theory::ppAssert(TrustNode tin,
                                        TrustSubstitutionMap& outSubstitutions)
{
  Assert(tin.getKind() == TrustNodeKind::LEMMA);
  TNode in = tin.getNode();
  if (in.getKind() == kind::EQUAL)
  {
    // (and (= x t) phi) can be replaced by phi[x/t] if
    // 1) x is a variable
    // 2) x is not in the term t
    // 3) x : T and t : S, then S <: T
    if (in[0].isVar() && isLegalElimination(in[0], in[1]))
    {
      outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].isVar() && isLegalElimination(in[1], in[0]))
    {
      outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
  }

  return PP_ASSERT_STATUS_UNSOLVED;
}

std::pair<bool, Node> Theory::entailmentCheck(TNode lit)
{
  return make_pair(false, Node::null());
}

void Theory::addCarePair(TNode t1, TNode t2) {
  Assert(d_careGraph != nullptr);
  Trace("sharing") << "Theory::addCarePair: add pair " << d_id << " " << t1
                   << " " << t2 << std::endl;
  d_careGraph->insert(CarePair(t1, t2, d_id));
}
void Theory::addCarePairArgs(TNode a, TNode b)
{
  Assert(d_careGraph != nullptr);
  Assert(d_equalityEngine != nullptr);
  Assert(a.hasOperator() && b.hasOperator());
  Assert(a.getOperator() == b.getOperator());
  Assert(a.getNumChildren() == b.getNumChildren());
  Trace("sharing") << "Theory::addCarePairArgs: checking function " << d_id
                   << " " << a << " " << b << std::endl;
  for (size_t k = 0, nchildren = a.getNumChildren(); k < nchildren; ++k)
  {
    TNode x = a[k];
    TNode y = b[k];
    if (d_equalityEngine->isTriggerTerm(x, d_id)
        && d_equalityEngine->isTriggerTerm(y, d_id)
        && !d_equalityEngine->areEqual(x, y))
    {
      TNode x_shared = d_equalityEngine->getTriggerTermRepresentative(x, d_id);
      TNode y_shared = d_equalityEngine->getTriggerTermRepresentative(y, d_id);
      addCarePair(x_shared, y_shared);
    }
  }
}

void Theory::processCarePairArgs(TNode a, TNode b)
{
  // if a and b are already equal, we ignore this pair
  if (d_theoryState->areEqual(a, b))
  {
    return;
  }
  // otherwise, we add pairs for each of their arguments
  addCarePairArgs(a, b);
}

bool Theory::areCareDisequal(TNode x, TNode y)
{
  Assert(d_equalityEngine != nullptr);
  Assert(d_equalityEngine->hasTerm(x));
  Assert(d_equalityEngine->hasTerm(y));
  Assert(x != y);
  Assert(!x.isConst() || !y.isConst());
  // first just check if they are disequal, which is sufficient for
  // non-shared terms.
  if (d_equalityEngine->areDisequal(x, y, false))
  {
    return true;
  }
  // if we aren't shared, we are not disequal
  if (!d_equalityEngine->isTriggerTerm(x, d_id)
      || !d_equalityEngine->isTriggerTerm(y, d_id))
  {
    return false;
  }
  // otherwise use getEqualityStatus to ask the appropriate theory whether
  // x and y are disequal.
  TNode x_shared = d_equalityEngine->getTriggerTermRepresentative(x, d_id);
  TNode y_shared = d_equalityEngine->getTriggerTermRepresentative(y, d_id);
  EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
  if (eqStatus == EQUALITY_FALSE_AND_PROPAGATED || eqStatus == EQUALITY_FALSE
      || eqStatus == EQUALITY_FALSE_IN_MODEL)
  {
    return true;
  }
  return false;
}

void Theory::getCareGraph(CareGraph* careGraph) {
  Assert(careGraph != nullptr);

  Trace("sharing") << "Theory<" << getId() << ">::getCareGraph()" << std::endl;
  TimerStat::CodeTimer computeCareGraphTime(d_computeCareGraphTime);
  d_careGraph = careGraph;
  computeCareGraph();
  d_careGraph = nullptr;
}

bool Theory::proofsEnabled() const
{
  return d_env.getProofNodeManager() != nullptr;
}

EqualityStatus Theory::getEqualityStatus(TNode a, TNode b)
{
  // if not using an equality engine, then by default we don't know the status
  if (d_equalityEngine == nullptr)
  {
    return EQUALITY_UNKNOWN;
  }
  Trace("sharing") << "Theory<" << getId() << ">::getEqualityStatus(" << a << ", " << b << ")" << std::endl;
  Assert(d_equalityEngine->hasTerm(a) && d_equalityEngine->hasTerm(b));

  // Check for equality (simplest)
  if (d_equalityEngine->areEqual(a, b))
  {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }

  // Check for disequality
  if (d_equalityEngine->areDisequal(a, b, false))
  {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }

  // All other terms are unknown, which is conservative. A theory may override
  // this method if it knows more information.
  return EQUALITY_UNKNOWN;
}

void Theory::check(Effort level)
{
  // see if we are already done (as an optimization)
  if (done() && level < EFFORT_FULL)
  {
    return;
  }
  Assert(d_theoryState!=nullptr);
  // standard calls for resource, stats
  d_out->spendResource(Resource::TheoryCheckStep);
  TimerStat::CodeTimer checkTimer(d_checkTime);
  Trace("theory-check") << "Theory::preCheck " << level << " " << d_id
                        << std::endl;
  // pre-check at level
  if (preCheck(level))
  {
    // check aborted for a theory-specific reason
    return;
  }
  Assert(d_theoryState != nullptr);
  Trace("theory-check") << "Theory::process fact queue " << d_id << std::endl;
  // process the pending fact queue
  while (!done() && !d_theoryState->isInConflict())
  {
    // Get the next assertion from the fact queue
    Assertion assertion = get();
    TNode fact = assertion.d_assertion;
    Trace("theory-check") << "Theory::preNotifyFact " << fact << " " << d_id
                          << std::endl;
    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];
    // call the pre-notify method
    if (preNotifyFact(atom, polarity, fact, assertion.d_isPreregistered, false))
    {
      // handled in theory-specific way that doesn't involve equality engine
      continue;
    }
    Trace("theory-check") << "Theory::assert " << fact << " " << d_id
                          << std::endl;
    // Theories that don't have an equality engine should always return true
    // for preNotifyFact
    Assert(d_equalityEngine != nullptr);
    // assert to the equality engine
    if (atom.getKind() == kind::EQUAL)
    {
      d_equalityEngine->assertEquality(atom, polarity, fact);
    }
    else
    {
      d_equalityEngine->assertPredicate(atom, polarity, fact);
    }
    Trace("theory-check") << "Theory::notifyFact " << fact << " " << d_id
                          << std::endl;
    // notify the theory of the new fact, which is not internal
    notifyFact(atom, polarity, fact, false);
  }
  Trace("theory-check") << "Theory::postCheck " << d_id << std::endl;
  // post-check at level
  postCheck(level);
  Trace("theory-check") << "Theory::finish check " << d_id << std::endl;
}

bool Theory::preCheck(Effort level) { return false; }

void Theory::postCheck(Effort level) {}

bool Theory::preNotifyFact(
    TNode atom, bool polarity, TNode fact, bool isPrereg, bool isInternal)
{
  return false;
}

void Theory::notifyFact(TNode atom, bool polarity, TNode fact, bool isInternal)
{
}

void Theory::preRegisterTerm(TNode node) {}

void Theory::addSharedTerm(TNode n)
{
  Trace("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")"
                   << std::endl;
  Trace("theory::assertions")
      << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << std::endl;
  d_sharedTerms.push_back(n);
  // now call theory-specific method notifySharedTerm
  notifySharedTerm(n);
  // if we have an equality engine, add the trigger term
  if (d_equalityEngine != nullptr)
  {
    d_equalityEngine->addTriggerTerm(n, d_id);
  }
}

eq::EqualityEngine* Theory::getEqualityEngine()
{
  // get the assigned equality engine, which is a pointer stored in this class
  return d_equalityEngine;
}

bool Theory::expUsingCentralEqualityEngine(TheoryId id)
{
  return id != THEORY_ARITH;
}

theory::Assertion Theory::get()
{
  Assert(!done()) << "Theory::get() called with assertion queue empty!";

  // Get the assertion
  Assertion fact = d_facts[d_factsHead];
  d_factsHead = d_factsHead + 1;

  Trace("theory") << "Theory::get() => " << fact << " ("
                  << d_facts.size() - d_factsHead << " left)" << std::endl;

  return fact;
}

}  // namespace theory
}  // namespace cvc5::internal
