/*********************                                                        */
/*! \file bv_subtheory_core.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Liana Hadarean, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_core.h"

#include "options/bv_options.h"
#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ext_theory.h"
#include "theory/theory_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool CoreSolverExtTheoryCallback::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node> >& exp)
{
  if (d_equalityEngine == nullptr)
  {
    return false;
  }
  // get the constant equivalence classes
  bool retVal = false;
  for (const Node& n : vars)
  {
    if (d_equalityEngine->hasTerm(n))
    {
      Node nr = d_equalityEngine->getRepresentative(n);
      if (nr.isConst())
      {
        subs.push_back(nr);
        exp[n].push_back(n.eqNode(nr));
        retVal = true;
      }
      else
      {
        subs.push_back(n);
      }
    }
    else
    {
      subs.push_back(n);
    }
  }
  // return true if the substitution is non-trivial
  return retVal;
}

bool CoreSolverExtTheoryCallback::getReduction(int effort,
                                               Node n,
                                               Node& nr,
                                               bool& satDep)
{
  Trace("bv-ext") << "TheoryBV::checkExt : non-reduced : " << n << std::endl;
  if (n.getKind() == kind::BITVECTOR_TO_NAT)
  {
    nr = utils::eliminateBv2Nat(n);
    satDep = false;
    return true;
  }
  else if (n.getKind() == kind::INT_TO_BITVECTOR)
  {
    nr = utils::eliminateInt2Bv(n);
    satDep = false;
    return true;
  }
  return false;
}

CoreSolver::CoreSolver(context::Context* c, BVSolverLazy* bv)
    : SubtheorySolver(c, bv),
      d_notify(*this),
      d_isComplete(c, true),
      d_lemmaThreshold(16),
      d_preregisterCalled(false),
      d_checkCalled(false),
      d_bv(bv),
      d_extTheoryCb(),
      d_extTheory(new ExtTheory(d_extTheoryCb,
                                bv->d_bv.getSatContext(),
                                bv->d_bv.getUserContext(),
                                bv->d_bv.getOutputChannel())),
      d_reasons(c),
      d_needsLastCallCheck(false),
      d_extf_range_infer(bv->d_bv.getUserContext()),
      d_extf_collapse_infer(bv->d_bv.getUserContext())
{
  d_extTheory->addFunctionKind(kind::BITVECTOR_TO_NAT);
  d_extTheory->addFunctionKind(kind::INT_TO_BITVECTOR);
}

CoreSolver::~CoreSolver() {}

bool CoreSolver::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::bv::ee";
  return true;
}

void CoreSolver::finishInit()
{
  // use the parent's equality engine, which may be the one we allocated above
  d_equalityEngine = d_bv->d_bv.getEqualityEngine();

  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::BITVECTOR_CONCAT, true);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_AND);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_OR);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_XOR);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_NOT);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_NAND);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_NOR);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_XNOR);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_COMP);
  d_equalityEngine->addFunctionKind(kind::BITVECTOR_MULT, true);
  d_equalityEngine->addFunctionKind(kind::BITVECTOR_PLUS, true);
  d_equalityEngine->addFunctionKind(kind::BITVECTOR_EXTRACT, true);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SUB);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_NEG);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_UDIV);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_UREM);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SDIV);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SREM);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SMOD);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SHL);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_LSHR);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_ASHR);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_ULT);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_ULE);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_UGT);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_UGE);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SLT);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SLE);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SGT);
  //    d_equalityEngine->addFunctionKind(kind::BITVECTOR_SGE);
  d_equalityEngine->addFunctionKind(kind::BITVECTOR_TO_NAT);
  d_equalityEngine->addFunctionKind(kind::INT_TO_BITVECTOR);
}

void CoreSolver::preRegister(TNode node) {
  d_preregisterCalled = true;
  if (node.getKind() == kind::EQUAL) {
    d_equalityEngine->addTriggerPredicate(node);
  } else {
    d_equalityEngine->addTerm(node);
    // Register with the extended theory, for context-dependent simplification.
    // Notice we do this for registered terms but not internally generated
    // equivalence classes. The two should roughly cooincide. Since ExtTheory is
    // being used as a heuristic, it is good enough to be registered here.
    d_extTheory->registerTerm(node);
  }
}


void CoreSolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions);
  }
}

bool CoreSolver::check(Theory::Effort e) {
  Trace("bitvector::core") << "CoreSolver::check \n";

  d_bv->d_inferManager.spendResource(
      ResourceManager::Resource::TheoryCheckStep);

  d_checkCalled = true;
  Assert(!d_bv->inConflict());
  ++(d_statistics.d_numCallstoCheck);
  bool ok = true;
  std::vector<Node> core_eqs;
  TNodeBoolMap seen;
  while (! done()) {
    TNode fact = get();
    if (d_isComplete && !isCompleteForTerm(fact, seen)) {
      d_isComplete = false;
    }
    
    // only reason about equalities
    if (fact.getKind() == kind::EQUAL || (fact.getKind() == kind::NOT && fact[0].getKind() == kind::EQUAL)) {
      ok = assertFactToEqualityEngine(fact, fact);
    } else {
      ok = assertFactToEqualityEngine(fact, fact);
    }
    if (!ok)
      return false;
  }

  if (Theory::fullEffort(e) && isComplete()) {
    buildModel();
  }

  return true;
}

void CoreSolver::buildModel()
{
  Debug("bv-core") << "CoreSolver::buildModel() \n";
  NodeManager* nm = NodeManager::currentNM();
  d_modelValues.clear();
  TNodeSet constants;
  TNodeSet constants_in_eq_engine;
  // collect constants in equality engine
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while (!eqcs_i.isFinished())
  {
    TNode repr = *eqcs_i;
    if (repr.getKind() == kind::CONST_BITVECTOR)
    {
      // must check if it's just the constant
      eq::EqClassIterator it(repr, d_equalityEngine);
      if (!(++it).isFinished() || true)
      {
        constants.insert(repr);
        constants_in_eq_engine.insert(repr);
      }
    }
    ++eqcs_i;
  }

  // build repr to value map

  eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while (!eqcs_i.isFinished())
  {
    TNode repr = *eqcs_i;
    ++eqcs_i;

    if (!repr.isVar() && repr.getKind() != kind::CONST_BITVECTOR
        && !d_bv->isSharedTerm(repr))
    {
      continue;
    }

    TypeNode type = repr.getType();
    if (type.isBitVector() && repr.getKind() != kind::CONST_BITVECTOR)
    {
      Debug("bv-core-model") << "   processing " << repr << "\n";
      // we need to assign a value for it
      TypeEnumerator te(type);
      Node val;
      do
      {
        val = *te;
        ++te;
        // Debug("bv-core-model") << "  trying value " << val << "\n";
        // Debug("bv-core-model") << "  is in set? " << constants.count(val) <<
        // "\n"; Debug("bv-core-model") << "  enumerator done? " <<
        // te.isFinished() << "\n";
      } while (constants.count(val) != 0 && !(te.isFinished()));

      if (te.isFinished() && constants.count(val) != 0)
      {
        // if we cannot enumerate anymore values we just return the lemma
        // stating that at least two of the representatives are equal.
        std::vector<TNode> representatives;
        representatives.push_back(repr);

        for (TNodeSet::const_iterator it = constants_in_eq_engine.begin();
             it != constants_in_eq_engine.end();
             ++it)
        {
          TNode constant = *it;
          if (utils::getSize(constant) == utils::getSize(repr))
          {
            representatives.push_back(constant);
          }
        }
        for (ModelValue::const_iterator it = d_modelValues.begin();
             it != d_modelValues.end();
             ++it)
        {
          representatives.push_back(it->first);
        }
        std::vector<Node> equalities;
        for (unsigned i = 0; i < representatives.size(); ++i)
        {
          for (unsigned j = i + 1; j < representatives.size(); ++j)
          {
            TNode a = representatives[i];
            TNode b = representatives[j];
            if (a.getKind() == kind::CONST_BITVECTOR
                && b.getKind() == kind::CONST_BITVECTOR)
            {
              Assert(a != b);
              continue;
            }
            if (utils::getSize(a) == utils::getSize(b))
            {
              equalities.push_back(nm->mkNode(kind::EQUAL, a, b));
            }
          }
        }
        // better off letting the SAT solver split on values
        if (equalities.size() > d_lemmaThreshold)
        {
          d_isComplete = false;
          return;
        }

        if (equalities.size() == 0)
        {
          Debug("bv-core") << "  lemma: true (no equalities)" << std::endl;
        }
        else
        {
          Node lemma = utils::mkOr(equalities);
          d_bv->lemma(lemma);
          Debug("bv-core") << "  lemma: " << lemma << std::endl;
        }
        return;
      }

      Debug("bv-core-model") << "   " << repr << " => " << val << "\n";
      constants.insert(val);
      d_modelValues[repr] = val;
    }
  }
}

bool CoreSolver::assertFactToEqualityEngine(TNode fact, TNode reason) {
  // Notify the equality engine
  if (!d_bv->inConflict()
      && (!d_bv->wasPropagatedBySubtheory(fact)
          || d_bv->getPropagatingSubtheory(fact) != SUB_CORE))
  {
    Debug("bv-slicer-eq") << "CoreSolver::assertFactToEqualityEngine fact=" << fact << endl;
    // Debug("bv-slicer-eq") << "                     reason=" << reason << endl;
    bool negated = fact.getKind() == kind::NOT;
    TNode predicate = negated ? fact[0] : fact;
    if (predicate.getKind() == kind::EQUAL) {
      if (negated) {
        // dis-equality
        d_equalityEngine->assertEquality(predicate, false, reason);
      } else {
        // equality
        d_equalityEngine->assertEquality(predicate, true, reason);
      }
    } else {
      // Adding predicate if the congruence over it is turned on
      if (d_equalityEngine->isFunctionKind(predicate.getKind()))
      {
        d_equalityEngine->assertPredicate(predicate, !negated, reason);
      }
    }
  }

  // checking for a conflict
  if (d_bv->inConflict())
  {
    return false;
  }
  return true;
}

bool CoreSolver::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value) {
  Debug("bitvector::core") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false" ) << ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(predicate);
  }
  return d_solver.storePropagation(predicate.notNode());
}

bool CoreSolver::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
  Debug("bitvector::core") << "NotifyClass::eqNotifyTriggerTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(t1.eqNode(t2));
  } else {
    return d_solver.storePropagation(t1.eqNode(t2).notNode());
  }
}

void CoreSolver::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  d_solver.conflict(t1, t2);
}

bool CoreSolver::storePropagation(TNode literal) {
  return d_bv->storePropagation(literal, SUB_CORE);
}

void CoreSolver::conflict(TNode a, TNode b) {
  std::vector<TNode> assumptions;
  d_equalityEngine->explainEquality(a, b, true, assumptions);
  Node conflict = flattenAnd(assumptions);
  d_bv->setConflict(conflict);
}

bool CoreSolver::isCompleteForTerm(TNode term, TNodeBoolMap& seen) {
  return utils::isEqualityTerm(term, seen); 
}

bool CoreSolver::collectModelValues(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  if (Debug.isOn("bitvector-model")) {
    context::CDQueue<Node>::const_iterator it = d_assertionQueue.begin();
    for (; it!= d_assertionQueue.end(); ++it) {
      Debug("bitvector-model")
          << "CoreSolver::collectModelValues (assert " << *it << ")\n";
    }
  }
  if (isComplete()) {
    Debug("bitvector-model") << "CoreSolver::collectModelValues complete.";
    for (ModelValue::const_iterator it = d_modelValues.begin(); it != d_modelValues.end(); ++it) {
      Node a = it->first;
      Node b = it->second;
      Debug("bitvector-model") << "CoreSolver::collectModelValues modelValues "
                               << a << " => " << b << ")\n";
      if (!m->assertEquality(a, b, true))
      {
        return false;
      }
    }
  }
  return true;
}

Node CoreSolver::getModelValue(TNode var) {
  Debug("bitvector-model") << "CoreSolver::getModelValue (" << var <<")";
  Assert(isComplete());
  TNode repr = d_equalityEngine->getRepresentative(var);
  Node result = Node();
  if (repr.getKind() == kind::CONST_BITVECTOR) {
    result = repr;
  } else if (d_modelValues.find(repr) == d_modelValues.end()) {
    // it may be a shared term that never gets asserted
    // result is just Null
    Assert(d_bv->isSharedTerm(var));
  } else {
    result = d_modelValues[repr];
  }
  Debug("bitvector-model") << " => " << result <<"\n";
  return result;
}

EqualityStatus CoreSolver::getEqualityStatus(TNode a, TNode b)
{
  if (d_equalityEngine->areEqual(a, b))
  {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine->areDisequal(a, b, false))
  {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_UNKNOWN;
}

bool CoreSolver::hasTerm(TNode node) const
{
  return d_equalityEngine->hasTerm(node);
}
void CoreSolver::addTermToEqualityEngine(TNode node)
{
  d_equalityEngine->addTerm(node);
}

CoreSolver::Statistics::Statistics()
  : d_numCallstoCheck("theory::bv::CoreSolver::NumCallsToCheck", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numCallstoCheck);
}
CoreSolver::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numCallstoCheck);
}

void CoreSolver::checkExtf(Theory::Effort e)
{
  if (e == Theory::EFFORT_LAST_CALL)
  {
    std::vector<Node> nred = d_extTheory->getActive();
    doExtfReductions(nred);
  }
  Assert(e == Theory::EFFORT_FULL);
  // do inferences (adds external lemmas)  TODO: this can be improved to add
  // internal inferences
  std::vector<Node> nred;
  if (d_extTheory->doInferences(0, nred))
  {
    return;
  }
  d_needsLastCallCheck = false;
  if (!nred.empty())
  {
    // other inferences involving bv2nat, int2bv
    if (options::bvAlgExtf())
    {
      if (doExtfInferences(nred))
      {
        return;
      }
    }
    if (!options::bvLazyReduceExtf())
    {
      if (doExtfReductions(nred))
      {
        return;
      }
    }
    else
    {
      d_needsLastCallCheck = true;
    }
  }
}

bool CoreSolver::needsCheckLastEffort() const { return d_needsLastCallCheck; }

bool CoreSolver::doExtfInferences(std::vector<Node>& terms)
{
  NodeManager* nm = NodeManager::currentNM();
  bool sentLemma = false;
  eq::EqualityEngine* ee = d_equalityEngine;
  std::map<Node, Node> op_map;
  for (unsigned j = 0; j < terms.size(); j++)
  {
    TNode n = terms[j];
    Assert(n.getKind() == kind::BITVECTOR_TO_NAT
           || n.getKind() == kind::INT_TO_BITVECTOR);
    if (n.getKind() == kind::BITVECTOR_TO_NAT)
    {
      // range lemmas
      if (d_extf_range_infer.find(n) == d_extf_range_infer.end())
      {
        d_extf_range_infer.insert(n);
        unsigned bvs = n[0].getType().getBitVectorSize();
        Node min = nm->mkConst(Rational(0));
        Node max = nm->mkConst(Rational(Integer(1).multiplyByPow2(bvs)));
        Node lem = nm->mkNode(kind::AND,
                              nm->mkNode(kind::GEQ, n, min),
                              nm->mkNode(kind::LT, n, max));
        Trace("bv-extf-lemma")
            << "BV extf lemma (range) : " << lem << std::endl;
        d_bv->d_inferManager.lemma(lem);
        sentLemma = true;
      }
    }
    Node r = (ee && ee->hasTerm(n[0])) ? ee->getRepresentative(n[0]) : n[0];
    op_map[r] = n;
  }
  for (unsigned j = 0; j < terms.size(); j++)
  {
    TNode n = terms[j];
    Node r = (ee && ee->hasTerm(n[0])) ? ee->getRepresentative(n) : n;
    std::map<Node, Node>::iterator it = op_map.find(r);
    if (it != op_map.end())
    {
      Node parent = it->second;
      // Node cterm = parent[0]==n ? parent : nm->mkNode( parent.getOperator(),
      // n );
      Node cterm = parent[0].eqNode(n);
      Trace("bv-extf-lemma-debug")
          << "BV extf collapse based on : " << cterm << std::endl;
      if (d_extf_collapse_infer.find(cterm) == d_extf_collapse_infer.end())
      {
        d_extf_collapse_infer.insert(cterm);

        Node t = n[0];
        if (t.getType() == parent.getType())
        {
          if (n.getKind() == kind::INT_TO_BITVECTOR)
          {
            Assert(t.getType().isInteger());
            // congruent modulo 2^( bv width )
            unsigned bvs = n.getType().getBitVectorSize();
            Node coeff = nm->mkConst(Rational(Integer(1).multiplyByPow2(bvs)));
            Node k = nm->mkSkolem(
                "int_bv_cong", t.getType(), "for int2bv/bv2nat congruence");
            t = nm->mkNode(kind::PLUS, t, nm->mkNode(kind::MULT, coeff, k));
          }
          Node lem = parent.eqNode(t);

          if (parent[0] != n)
          {
            Assert(ee->areEqual(parent[0], n));
            lem = nm->mkNode(kind::IMPLIES, parent[0].eqNode(n), lem);
          }
          // this handles inferences of the form, e.g.:
          //   ((_ int2bv w) (bv2nat x)) == x (if x is bit-width w)
          //   (bv2nat ((_ int2bv w) x)) == x + k*2^w for some k
          Trace("bv-extf-lemma")
              << "BV extf lemma (collapse) : " << lem << std::endl;
          d_bv->d_inferManager.lemma(lem);
          sentLemma = true;
        }
      }
      Trace("bv-extf-lemma-debug")
          << "BV extf f collapse based on : " << cterm << std::endl;
    }
  }
  return sentLemma;
}

bool CoreSolver::doExtfReductions(std::vector<Node>& terms)
{
  std::vector<Node> nredr;
  if (d_extTheory->doReductions(0, terms, nredr))
  {
    return true;
  }
  Assert(nredr.empty());
  return false;
}
