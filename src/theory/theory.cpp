/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "smt/smt_statistics_registry.h"
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

namespace cvc5 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::s_uninterpretedSortOwner = THEORY_UF;

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
               context::Context* satContext,
               context::UserContext* userContext,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo,
               ProofNodeManager* pnm,
               std::string name)
    : d_id(id),
      d_satContext(satContext),
      d_userContext(userContext),
      d_logicInfo(logicInfo),
      d_facts(satContext),
      d_factsHead(satContext, 0),
      d_sharedTermsIndex(satContext, 0),
      d_careGraph(nullptr),
      d_instanceName(name),
      d_checkTime(smtStatisticsRegistry().registerTimer(getStatsPrefix(id)
                                                        + name + "checkTime")),
      d_computeCareGraphTime(smtStatisticsRegistry().registerTimer(
          getStatsPrefix(id) + name + "computeCareGraphTime")),
      d_sharedTerms(satContext),
      d_out(&out),
      d_valuation(valuation),
      d_equalityEngine(nullptr),
      d_allocEqualityEngine(nullptr),
      d_theoryState(nullptr),
      d_inferManager(nullptr),
      d_quantEngine(nullptr),
      d_pnm(pnm)
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
    // always associated with the same SAT context as the theory (d_satContext)
    d_allocEqualityEngine.reset(new eq::EqualityEngine(
        *esi.d_notify, d_satContext, esi.d_name, esi.d_constantsAreTriggers));
    // use it as the official equality engine
    setEqualityEngine(d_allocEqualityEngine.get());
  }
  finishInit();
}

TheoryId Theory::theoryOf(options::TheoryOfMode mode, TNode node)
{
  TheoryId tid = THEORY_BUILTIN;
  switch(mode) {
    case options::TheoryOfMode::THEORY_OF_TYPE_BASED:
      // Constants, variables, 0-ary constructors
      if (node.isVar())
      {
        if (node.getKind() == kind::BOOLEAN_TERM_VARIABLE)
        {
          tid = THEORY_UF;
        }
        else
        {
          tid = Theory::theoryOf(node.getType());
        }
      }
      else if (node.getKind() == kind::EQUAL)
      {
        // Equality is owned by the theory that owns the domain
        tid = Theory::theoryOf(node[0].getType());
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
        if (Theory::theoryOf(node.getType()) != theory::THEORY_BOOL)
        {
          // We treat the variables as uninterpreted
          tid = s_uninterpretedSortOwner;
        }
        else
        {
          if (node.getKind() == kind::BOOLEAN_TERM_VARIABLE)
          {
            // Boolean vars go to UF
            tid = THEORY_UF;
          }
          else
          {
            // Except for the Boolean ones
            tid = THEORY_BOOL;
          }
        }
      }
      else if (node.getKind() == kind::EQUAL)
      {  // Equality
        // If one of them is an ITE, it's irelevant, since they will get
        // replaced out anyhow
        if (node[0].getKind() == kind::ITE)
        {
          tid = Theory::theoryOf(node[0].getType());
        }
        else if (node[1].getKind() == kind::ITE)
        {
          tid = Theory::theoryOf(node[1].getType());
        }
        else
        {
          TNode l = node[0];
          TNode r = node[1];
          TypeNode ltype = l.getType();
          TypeNode rtype = r.getType();
          // If the types are different, we must assign based on type due
          // to handling subtypes (limited to arithmetic). Also, if we are
          // a Boolean equality, we must assign THEORY_BOOL.
          if (ltype != rtype || ltype.isBoolean())
          {
            tid = Theory::theoryOf(ltype);
          }
          else
          {
            // If both sides belong to the same theory the choice is easy
            TheoryId T1 = Theory::theoryOf(l);
            TheoryId T2 = Theory::theoryOf(r);
            if (T1 == T2)
            {
              tid = T1;
            }
            else
            {
              TheoryId T3 = Theory::theoryOf(ltype);
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
  Trace("theory::internal") << "theoryOf(" << mode << ", " << node << ") -> " << tid << std::endl;
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
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << endl;
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
  DebugChannel.getStream() << "Theory::debugPrintFacts()" << endl;
  printFacts(DebugChannel.getStream());
}

bool Theory::isLegalElimination(TNode x, TNode val)
{
  Assert(x.isVar());
  if (x.getKind() == kind::BOOLEAN_TERM_VARIABLE
      || val.getKind() == kind::BOOLEAN_TERM_VARIABLE)
  {
    return false;
  }
  if (expr::hasSubterm(val, x))
  {
    return false;
  }
  if (!val.getType().isSubtypeOf(x.getType()))
  {
    return false;
  }
  if (!options::produceModels() && !d_logicInfo.isQuantified())
  {
    // Don't care about the model and logic is not quantified, we can eliminate.
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
  if (d_equalityEngine != nullptr)
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

bool Theory::collectModelValues(TheoryModel* m, const std::set<Node>& termSet)
{
  return true;
}

Theory::PPAssertStatus Theory::ppAssert(TrustNode tin,
                                        TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  if (in.getKind() == kind::EQUAL)
  {
    // (and (= x t) phi) can be replaced by phi[x/t] if
    // 1) x is a variable
    // 2) x is not in the term t
    // 3) x : T and t : S, then S <: T
    if (in[0].isVar() && isLegalElimination(in[0], in[1])
        && in[0].getKind() != kind::BOOLEAN_TERM_VARIABLE)
    {
      outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].isVar() && isLegalElimination(in[1], in[0])
        && in[1].getKind() != kind::BOOLEAN_TERM_VARIABLE)
    {
      outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[0].isConst() && in[1].isConst())
    {
      if (in[0] != in[1])
      {
        return PP_ASSERT_STATUS_CONFLICT;
      }
    }
  }
  else if (in.getKind() == kind::NOT && in[0].getKind() == kind::EQUAL
           && in[0][0].getType().isBoolean())
  {
    TNode eq = in[0];
    if (eq[0].isVar())
    {
      Node res = eq[0].eqNode(eq[1].notNode());
      TrustNode tn = TrustNode::mkTrustRewrite(in, res, nullptr);
      return ppAssert(tn, outSubstitutions);
    }
    else if (eq[1].isVar())
    {
      Node res = eq[1].eqNode(eq[0].notNode());
      TrustNode tn = TrustNode::mkTrustRewrite(in, res, nullptr);
      return ppAssert(tn, outSubstitutions);
    }
  }

  return PP_ASSERT_STATUS_UNSOLVED;
}

std::pair<bool, Node> Theory::entailmentCheck(TNode lit)
{
  return make_pair(false, Node::null());
}

void Theory::addCarePair(TNode t1, TNode t2) {
  if (d_careGraph) {
    d_careGraph->insert(CarePair(t1, t2, d_id));
  }
}

void Theory::getCareGraph(CareGraph* careGraph) {
  Assert(careGraph != NULL);

  Trace("sharing") << "Theory<" << getId() << ">::getCareGraph()" << std::endl;
  TimerStat::CodeTimer computeCareGraphTime(d_computeCareGraphTime);
  d_careGraph = careGraph;
  computeCareGraph();
  d_careGraph = NULL;
}

bool Theory::proofsEnabled() const
{
  return d_pnm != nullptr;
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
  Debug("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")"
                   << std::endl;
  Debug("theory::assertions")
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

}  // namespace theory
}  // namespace cvc5
