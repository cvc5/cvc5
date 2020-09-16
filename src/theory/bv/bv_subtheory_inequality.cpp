/*********************                                                        */
/*! \file bv_subtheory_inequality.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_inequality.h"

#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool InequalitySolver::check(Theory::Effort e) {
  Debug("bv-subtheory-inequality") << "InequalitySolveR::check("<< e <<")\n";
  TimerStat::CodeTimer inequalityTimer(d_statistics.d_solveTime);
  ++(d_statistics.d_numCallstoCheck);
  d_bv->spendResource(ResourceManager::Resource::TheoryCheckStep);

  bool ok = true;
  while (!done() && ok) {
    TNode fact = get();
    Debug("bv-subtheory-inequality") << "  "<< fact <<"\n";
    if (fact.getKind() == kind::EQUAL) {
      TNode a = fact[0];
      if( a.getType().isBitVector() ){
        TNode b = fact[1];
        ok = addInequality(a, b, false, fact);
        if (ok)
          ok = addInequality(b, a, false, fact);
      }
    } else if (fact.getKind() == kind::NOT && fact[0].getKind() == kind::EQUAL) {
      TNode a = fact[0][0];
      if( a.getType().isBitVector() ){
        TNode b = fact[0][1];
        ok = d_inequalityGraph.addDisequality(a, b, fact);
      }
    }
    if (fact.getKind() == kind::NOT && fact[0].getKind() == kind::BITVECTOR_ULE) {
      TNode a = fact[0][1];
      TNode b = fact[0][0];
      ok = addInequality(a, b, true, fact);
      // propagate
      // NodeManager *nm = NodeManager::currentNM();
      // if (d_bv->isSharedTerm(a) && d_bv->isSharedTerm(b)) {
      //   Node neq = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, a, b));
      //   d_bv->storePropagation(neq, SUB_INEQUALITY);
      //   d_explanations[neq] = fact;
      // }
    } else if (fact.getKind() == kind::NOT && fact[0].getKind() == kind::BITVECTOR_ULT) {
      TNode a = fact[0][1];
      TNode b = fact[0][0];
      ok = addInequality(a, b, false, fact);
    } else if (fact.getKind() == kind::BITVECTOR_ULT) {
      TNode a = fact[0];
      TNode b = fact[1];
      ok = addInequality(a, b, true, fact);
      // propagate
      // if (d_bv->isSharedTerm(a) && d_bv->isSharedTerm(b)) {
      //   Node neq = nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, a, b));
      //   d_bv->storePropagation(neq, SUB_INEQUALITY);
      //   d_explanations[neq] = fact;
      // }
    } else if (fact.getKind() == kind::BITVECTOR_ULE) {
      TNode a = fact[0];
      TNode b = fact[1];
      ok = addInequality(a, b, false, fact);
    }
  }

  if (!ok) {
    std::vector<TNode> conflict;
    d_inequalityGraph.getConflict(conflict);
    Node confl = utils::flattenAnd(conflict);
    d_bv->setConflict(confl);
    Debug("bv-subtheory-inequality") << "InequalitySolver::conflict:  "<< confl <<"\n";
    return false;
  }

  if (isComplete() && Theory::fullEffort(e)) {
    // make sure all the disequalities we didn't split on are still satisifed
    // and split on the ones that are not
    std::vector<Node> lemmas;
    d_inequalityGraph.checkDisequalities(lemmas);
    for(unsigned i = 0; i < lemmas.size(); ++i) {
      d_bv->lemma(lemmas[i]);
    }
  }
  Debug("bv-subtheory-inequality") << "InequalitySolver done. ";
  return true;
}

EqualityStatus InequalitySolver::getEqualityStatus(TNode a, TNode b)
{
  if (!isComplete()) return EQUALITY_UNKNOWN;

  NodeManager* nm = NodeManager::currentNM();
  Node a_lt_b = nm->mkNode(kind::BITVECTOR_ULT, a, b);
  Node b_lt_a = nm->mkNode(kind::BITVECTOR_ULT, b, a);

  // if an inequality containing the terms has been asserted then we know
  // the equality is false
  if (d_assertionSet.contains(a_lt_b) || d_assertionSet.contains(b_lt_a))
  {
    return EQUALITY_FALSE;
  }

  if (!d_inequalityGraph.hasValueInModel(a)
      || !d_inequalityGraph.hasValueInModel(b))
  {
    return EQUALITY_UNKNOWN;
  }

  // TODO: check if this disequality is entailed by inequalities via
  // transitivity

  BitVector a_val = d_inequalityGraph.getValueInModel(a);
  BitVector b_val = d_inequalityGraph.getValueInModel(b);

  if (a_val == b_val)
  {
    return EQUALITY_TRUE_IN_MODEL;
  }
  else
  {
    return EQUALITY_FALSE_IN_MODEL;
  }
}

void InequalitySolver::assertFact(TNode fact) {
  d_assertionQueue.push_back(fact);
  d_assertionSet.insert(fact);
  if (!isInequalityOnly(fact)) {
    d_isComplete = false;
  }
}

bool InequalitySolver::isInequalityOnly(TNode node) {
  if (node.getKind() == kind::NOT) {
    node = node[0];
  }

  if (node.getAttribute(IneqOnlyComputedAttribute())) {
    return node.getAttribute(IneqOnlyAttribute());
  }

  if (node.getKind() != kind::EQUAL &&
      node.getKind() != kind::BITVECTOR_ULT &&
      node.getKind() != kind::BITVECTOR_ULE &&
      node.getKind() != kind::CONST_BITVECTOR &&
      node.getKind() != kind::SELECT &&
      node.getKind() != kind::STORE &&
      node.getMetaKind() != kind::metakind::VARIABLE) {
    // not worth caching
    return false;
  }
  bool res = true;
  for (unsigned i = 0; res && i < node.getNumChildren(); ++i) {
    res = res && isInequalityOnly(node[i]);
  }
  node.setAttribute(IneqOnlyComputedAttribute(), true);
  node.setAttribute(IneqOnlyAttribute(), res);
  return res;
}

void InequalitySolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  Assert(d_explanations.find(literal) != d_explanations.end());
  TNode explanation = d_explanations[literal];
  assumptions.push_back(explanation);
  Debug("bv-inequality-explain") << "InequalitySolver::explain " << literal << " with " << explanation <<"\n";
}

void InequalitySolver::propagate(Theory::Effort e) { Assert(false); }
bool InequalitySolver::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  Debug("bitvector-model") << "InequalitySolver::collectModelValues \n";
  std::vector<Node> model;
  d_inequalityGraph.getAllValuesInModel(model);
  for (unsigned i = 0; i < model.size(); ++i) {
    Assert(model[i].getKind() == kind::EQUAL);
    if (!m->assertEquality(model[i][0], model[i][1], true))
    {
      return false;
    }
  }
  return true;
}

Node InequalitySolver::getModelValue(TNode var) {
  Assert(isInequalityOnly(var));
  Debug("bitvector-model") << "InequalitySolver::getModelValue (" << var <<")";
  Assert(isComplete());
  Node result = Node();
  if (!d_inequalityGraph.hasValueInModel(var)) {
    Assert(d_bv->isSharedTerm(var));
  } else {
    BitVector val = d_inequalityGraph.getValueInModel(var);
    result = utils::mkConst(val);
  }
  Debug("bitvector-model") << " => " << result <<"\n";
  return result;
}

void InequalitySolver::preRegister(TNode node) {
  Kind kind = node.getKind(); 
  if (kind == kind::EQUAL ||
      kind == kind::BITVECTOR_ULE ||
      kind == kind::BITVECTOR_ULT) {
    d_ineqTerms.insert(node[0]);
    d_ineqTerms.insert(node[1]);
  }
}

bool InequalitySolver::addInequality(TNode a, TNode b, bool strict, TNode fact)
{
  bool ok = d_inequalityGraph.addInequality(a, b, strict, fact);
  if (!ok || !strict) return ok;

  Node one = utils::mkConst(utils::getSize(a), 1);
  Node a_plus_one = Rewriter::rewrite(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_PLUS, a, one));
  if (d_ineqTerms.find(a_plus_one) != d_ineqTerms.end())
  {
    ok = d_inequalityGraph.addInequality(a_plus_one, b, false, fact);
  }
  return ok;
}

InequalitySolver::Statistics::Statistics()
    : d_numCallstoCheck("theory::bv::inequality::NumCallsToCheck", 0),
      d_solveTime("theory::bv::inequality::SolveTime")
{
  smtStatisticsRegistry()->registerStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->registerStat(&d_solveTime);
}

InequalitySolver::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->unregisterStat(&d_solveTime);
}
