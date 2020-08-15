/*********************                                                        */
/*! \file theory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base for theory interface.
 **
 ** Base for theory interface.
 **/

#include "theory/theory.h"

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "options/theory_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/ext_theory.h"
#include "theory/quantifiers_engine.h"
#include "theory/substitutions.h"
#include "theory/theory_rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {

/** Default value for the uninterpreted sorts is the UF theory */
TheoryId Theory::s_uninterpretedSortOwner = THEORY_UF;

std::ostream& operator<<(std::ostream& os, Theory::Effort level){
  switch(level){
  case Theory::EFFORT_STANDARD:
    os << "EFFORT_STANDARD"; break;
  case Theory::EFFORT_FULL:
    os << "EFFORT_FULL"; break;
  case Theory::EFFORT_COMBINATION:
    os << "EFFORT_COMBINATION"; break;
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
      d_instanceName(name),
      d_satContext(satContext),
      d_userContext(userContext),
      d_logicInfo(logicInfo),
      d_pnm(pnm),
      d_facts(satContext),
      d_factsHead(satContext, 0),
      d_sharedTermsIndex(satContext, 0),
      d_careGraph(NULL),
      d_quantEngine(NULL),
      d_decManager(nullptr),
      d_checkTime(getStatsPrefix(id) + name + "::checkTime"),
      d_computeCareGraphTime(getStatsPrefix(id) + name
                             + "::computeCareGraphTime"),
      d_sharedTerms(satContext),
      d_out(&out),
      d_valuation(valuation),
      d_proofsEnabled(false)
{
  smtStatisticsRegistry()->registerStat(&d_checkTime);
  smtStatisticsRegistry()->registerStat(&d_computeCareGraphTime);
}

Theory::~Theory() {
  smtStatisticsRegistry()->unregisterStat(&d_checkTime);
  smtStatisticsRegistry()->unregisterStat(&d_computeCareGraphTime);
}

bool Theory::needsEqualityEngine(EeSetupInfo& esi) { return false; }

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
      else if (node.isConst())
      {
        tid = Theory::theoryOf(node.getType());
      }
      else if (node.getKind() == kind::EQUAL)
      {
        // Equality is owned by the theory that owns the domain
        tid = Theory::theoryOf(node[0].getType());
      }
      else
      {
        // Regular nodes are owned by the kind
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
      else if (node.isConst())
      {
        // Constants go to the theory of the type
        tid = Theory::theoryOf(node.getType());
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
          if (ltype != rtype)
          {
            tid = Theory::theoryOf(l.getType());
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
        // Regular nodes are owned by the kind
        tid = kindToTheoryId(node.getKind());
      }
    break;
  default:
    Unreachable();
  }
  Trace("theory::internal") << "theoryOf(" << mode << ", " << node << ") -> " << tid << std::endl;
  return tid;
}

void Theory::addSharedTermInternal(TNode n) {
  Debug("sharing") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << endl;
  Debug("theory::assertions") << "Theory::addSharedTerm<" << getId() << ">(" << n << ")" << endl;
  d_sharedTerms.push_back(n);
  addSharedTerm(n);
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
  if (!options::produceModels())
  {
    // don't care about the model, we are fine
    return true;
  }
  // if there is a model object
  TheoryModel* tm = d_valuation.getModel();
  Assert(tm != nullptr);
  return tm->isLegalElimination(x, val);
}

std::unordered_set<TNode, TNodeHashFunction> Theory::currentlySharedTerms() const{
  std::unordered_set<TNode, TNodeHashFunction> currentlyShared;
  for (shared_terms_iterator i = shared_terms_begin(),
           i_end = shared_terms_end(); i != i_end; ++i) {
    currentlyShared.insert (*i);
  }
  return currentlyShared;
}

void Theory::collectTerms(TNode n,
                          set<Kind>& irrKinds,
                          set<Node>& termSet) const
{
  if (termSet.find(n) != termSet.end()) {
    return;
  }
  Kind nk = n.getKind();
  if (irrKinds.find(nk) == irrKinds.end())
  {
    Trace("theory::collectTerms")
        << "Theory::collectTerms: adding " << n << endl;
    termSet.insert(n);
  }
  if (nk == kind::NOT || nk == kind::EQUAL || !isLeaf(n))
  {
    for(TNode::iterator child_it = n.begin(); child_it != n.end(); ++child_it) {
      collectTerms(*child_it, irrKinds, termSet);
    }
  }
}


void Theory::computeRelevantTerms(set<Node>& termSet, bool includeShared) const
{
  set<Kind> irrKinds;
  computeRelevantTerms(termSet, irrKinds, includeShared);
}

void Theory::computeRelevantTerms(set<Node>& termSet,
                                  set<Kind>& irrKinds,
                                  bool includeShared) const
{
  // Collect all terms appearing in assertions
  irrKinds.insert(kind::EQUAL);
  irrKinds.insert(kind::NOT);
  context::CDList<Assertion>::const_iterator assert_it = facts_begin(), assert_it_end = facts_end();
  for (; assert_it != assert_it_end; ++assert_it) {
    collectTerms(*assert_it, irrKinds, termSet);
  }

  if (!includeShared) return;

  // Add terms that are shared terms
  set<Kind> kempty;
  context::CDList<TNode>::const_iterator shared_it = shared_terms_begin(), shared_it_end = shared_terms_end();
  for (; shared_it != shared_it_end; ++shared_it) {
    collectTerms(*shared_it, kempty, termSet);
  }
}

Theory::PPAssertStatus Theory::ppAssert(TNode in,
                                        SubstitutionMap& outSubstitutions)
{
  if (in.getKind() == kind::EQUAL)
  {
    // (and (= x t) phi) can be replaced by phi[x/t] if
    // 1) x is a variable
    // 2) x is not in the term t
    // 3) x : T and t : S, then S <: T
    if (in[0].isVar() && isLegalElimination(in[0], in[1])
        && in[0].getKind() != kind::BOOLEAN_TERM_VARIABLE)
    {
      outSubstitutions.addSubstitution(in[0], in[1]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].isVar() && isLegalElimination(in[1], in[0])
        && in[1].getKind() != kind::BOOLEAN_TERM_VARIABLE)
    {
      outSubstitutions.addSubstitution(in[1], in[0]);
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

void Theory::setQuantifiersEngine(QuantifiersEngine* qe) {
  Assert(d_quantEngine == NULL);
  Assert(qe != NULL);
  d_quantEngine = qe;
}

void Theory::setDecisionManager(DecisionManager* dm)
{
  Assert(d_decManager == nullptr);
  Assert(dm != nullptr);
  d_decManager = dm;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
