/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of separation logic.
 */

#include "theory/sep/theory_sep.h"

#include <map>

#include "base/map_util.h"
#include "expr/emptyset.h"
#include "expr/kind.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/smt_options.h"
#include "smt/logic_exception.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/sep/theory_sep_rewriter.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"
#include "util/cardinality.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sep {

TheorySep::TheorySep(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_SEP, env, out, valuation),
      d_bounds_init(false),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::sep::"),
      d_notify(*this),
      d_reduce(userContext()),
      d_spatial_assertions(context()),
      d_bound_kind(bound_invalid),
      d_card_max(0)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // indicate we are using the default theory state object
  d_theoryState = &d_state;
  d_inferManager = &d_im;

  // initialize the heap types
  initializeHeapTypes();
}

TheorySep::~TheorySep() {
  for( std::map< Node, HeapAssertInfo * >::iterator it = d_eqc_info.begin(); it != d_eqc_info.end(); ++it ){
    delete it->second;
  }
}

void TheorySep::initializeHeapTypes()
{
  if (d_env.hasSepHeap())
  {
    // for now, we only allow heap constraints of one type
    d_type_ref = d_env.getSepLocType();
    d_type_data = d_env.getSepDataType();
    Trace("sep-type") << "Sep: assume location type " << d_type_ref
                      << " is associated with data type " << d_type_data
                      << std::endl;
    d_nil_ref =
        NodeManager::currentNM()->mkNullaryOperator(d_type_ref, SEP_NIL);
    d_bound_kind = bound_default;
  }
}

TheoryRewriter* TheorySep::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheorySep::getProofChecker() { return nullptr; }

bool TheorySep::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::sep::ee";
  esi.d_notifyMerge = true;
  return true;
}

void TheorySep::finishInit()
{
  Assert(d_equalityEngine != nullptr);
  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(SEP_PTO);
  // we could but don't do congruence on SEP_STAR here.

  // separation logic predicates are not relevant for model building
  d_valuation.setIrrelevantKind(SEP_STAR);
  d_valuation.setIrrelevantKind(SEP_WAND);
  d_valuation.setIrrelevantKind(SEP_LABEL);
  d_valuation.setIrrelevantKind(SEP_PTO);
}

void TheorySep::preRegisterTerm(TNode n)
{
  Kind k = n.getKind();
  if (k == SEP_PTO || k == SEP_EMP || k == SEP_STAR || k == SEP_WAND)
  {
    ensureHeapTypesFor(n);
  }
}

bool TheorySep::propagateLit(TNode literal)
{
  return d_im.propagateLit(literal);
}

TrustNode TheorySep::explain(TNode literal)
{
  Trace("sep") << "TheorySep::explain(" << literal << ")" << std::endl;
  return d_im.explainLit(literal);
}


/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////

void TheorySep::computeCareGraph() {
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


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

void TheorySep::postProcessModel( TheoryModel* m ){
  Trace("sep-model") << "Printing model for TheorySep..." << std::endl;
  if (d_type_ref.isNull())
  {
    return;
  }

  // loc -> { data_1, ..., data_n } where (not (pto loc data_1))...(not (pto loc
  // data_n))).
  std::map<Node, std::vector<Node> > heapLocsNegativePtos;
  // set up model
  Trace("sep-model") << "...preparing sep model..." << std::endl;
  // collect data points that are not pointed to
  for (context::CDList<Assertion>::const_iterator it = facts_begin();
       it != facts_end();
       ++it)
  {
    Node lit = (*it).d_assertion;
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    atom = atom.getKind() == SEP_LABEL ? atom[0] : atom;
    if (lit.getKind() == NOT && atom.getKind() == SEP_PTO)
    {
      Node v1 = m->getValue(atom[0]);
      Node v2 = m->getValue(atom[1]);
      Trace("sep-model") << v1 << " does not point-to " << v2 << std::endl;
      heapLocsNegativePtos[v1].push_back(v2);
    }
  }

  NodeManager* nm = NodeManager::currentNM();
  std::vector< Node > sep_children;
  Node m_neq;
  Node m_heap;
  // should only be constructing for one heap type
  Assert(m_heap.isNull());
  Trace("sep-model") << "Model for heap, type = " << d_type_ref
                     << " with data type " << d_type_data << " : " << std::endl;
  computeLabelModel(d_base_label);
  HeapInfo& hm = d_label_model[d_base_label];
  if (hm.d_heap_locs_model.empty())
  {
    Trace("sep-model") << "  [empty]" << std::endl;
  }
  else
  {
    for (const Node& hv : hm.d_heap_locs_model)
    {
      Assert(hv.getKind() == SET_SINGLETON);
      std::vector<Node> pto_children;
      Node l = hv[0];
      Assert(l.isConst());
      pto_children.push_back(l);
      Trace("sep-model") << " " << l << " -> ";
      if (d_pto_model[l].isNull())
      {
        Trace("sep-model") << "_";
        TypeEnumerator te_range(d_type_data);
        if (d_env.isFiniteType(d_type_data))
        {
          pto_children.push_back(*te_range);
        }else{
          // must enumerate until we find one that is not explicitly pointed to
          bool success = false;
          Node cv;
          do
          {
            cv = *te_range;
            if (std::find(heapLocsNegativePtos[l].begin(),
                          heapLocsNegativePtos[l].end(),
                          cv)
                == heapLocsNegativePtos[l].end())
            {
              success = true;
            }
            else
            {
              ++te_range;
            }
          } while (!success);
          pto_children.push_back(cv);
        }
      }
      else
      {
        Trace("sep-model") << d_pto_model[l];
        Node vpto = m->getValue(d_pto_model[l]);
        Assert(vpto.isConst());
        pto_children.push_back(vpto);
      }
      Trace("sep-model") << std::endl;
      sep_children.push_back(
          NodeManager::currentNM()->mkNode(SEP_PTO, pto_children));
    }
  }
  Assert(!d_nil_ref.isNull());
  Node vnil = d_valuation.getModel()->getRepresentative(d_nil_ref);
  m_neq = nm->mkNode(EQUAL, d_nil_ref, vnil);
  Trace("sep-model") << "sep.nil = " << vnil << std::endl;
  Trace("sep-model") << std::endl;
  if (sep_children.empty())
  {
    TypeNode boolType = nm->booleanType();
    m_heap = nm->mkNullaryOperator(boolType, SEP_EMP);
  }
  else if (sep_children.size() == 1)
  {
    m_heap = sep_children[0];
  }
  else
  {
    m_heap = nm->mkNode(SEP_STAR, sep_children);
  }
  m->setHeapModel(m_heap, m_neq);

  Trace("sep-model") << "Finished printing model for TheorySep." << std::endl;
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheorySep::presolve() {
  Trace("sep-pp") << "Presolving" << std::endl;
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

bool TheorySep::preNotifyFact(
    TNode atom, bool polarity, TNode fact, bool isPrereg, bool isInternal)
{
  TNode satom = atom.getKind() == SEP_LABEL ? atom[0] : atom;
  TNode slbl = atom.getKind() == SEP_LABEL ? atom[1] : TNode::null();
  bool isSpatial = isSpatialKind(satom.getKind());
  if (isSpatial)
  {
    reduceFact(atom, polarity, fact);
    if (!slbl.isNull())
    {
      d_spatial_assertions.push_back(fact);
    }
  }
  if (!slbl.isNull() && satom.getKind() == SEP_PTO)
  {
    return false;
  }
  // assert to equality if non-spatial or a labelled pto
  if (!isSpatial)
  {
    return false;
  }
  // otherwise, maybe propagate
  doPending();
  return true;
}

void TheorySep::notifyFact(TNode atom,
                           bool polarity,
                           TNode fact,
                           bool isInternal)
{
  TNode satom = atom.getKind() == SEP_LABEL ? atom[0] : atom;
  if (atom.getKind() == SEP_LABEL && atom[0].getKind() == SEP_PTO)
  {
    // associate the equivalence class of the lhs with this pto
    Node r = getRepresentative(atom[1]);
    HeapAssertInfo* e = getOrMakeEqcInfo(r, true);
    if (checkPto(e, atom, polarity))
    {
      NodeList& elist = polarity ? e->d_posPto : e->d_negPto;
      elist.push_back(atom);
    }
  }
  // maybe propagate
  doPending();
}

void TheorySep::reduceFact(TNode atom, bool polarity, TNode fact)
{
  if (d_reduce.find(fact) != d_reduce.end())
  {
    // already reduced
    return;
  }
  d_reduce.insert(fact);
  TNode satom = atom.getKind() == SEP_LABEL ? atom[0] : atom;
  TNode slbl = atom.getKind() == SEP_LABEL ? atom[1] : TNode::null();
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  if (slbl.isNull())
  {
    Trace("sep-lemma-debug")
        << "Reducing unlabelled assertion " << atom << std::endl;
    // introduce top-level label, add iff
    Trace("sep-lemma-debug")
        << "...reference type is : " << d_type_ref << std::endl;
    Node b_lbl = getBaseLabel();
    Node satom_new = nm->mkNode(SEP_LABEL, satom, b_lbl);
    Node lem;
    Trace("sep-lemma-debug") << "...polarity is " << polarity << std::endl;
    if (polarity)
    {
      lem = nm->mkNode(OR, satom.negate(), satom_new);
    }
    else
    {
      lem = nm->mkNode(OR, satom, satom_new.negate());
    }
    Trace("sep-lemma-debug")
        << "Sep::Lemma : base reduction : " << lem << std::endl;
    d_im.lemma(lem, InferenceId::SEP_LABEL_INTRO);
    return;
  }
  Trace("sep-lemma-debug") << "Reducing assertion " << fact << std::endl;
  Node conc;
  if (Node* in_map = FindOrNull(d_red_conc[slbl], satom))
  {
    conc = *in_map;
  }
  else
  {
    // make conclusion based on type of assertion
    if (satom.getKind() == SEP_STAR || satom.getKind() == SEP_WAND)
    {
      if (!d_reference_bound_max.isNull())
      {
        Node blem = nm->mkNode(SET_SUBSET, slbl, d_reference_bound_max);
        d_im.lemma(blem, InferenceId::SEP_LABEL_DEF);
      }
      std::vector<Node> children;
      std::vector<Node> labels;
      getLabelChildren(satom, slbl, children, labels);
      Node empSet = nm->mkConst(EmptySet(slbl.getType()));
      Assert(children.size() > 1);
      if (satom.getKind() == SEP_STAR)
      {
        // make disjoint heap
        makeDisjointHeap(slbl, labels);
      }
      else
      {
        Assert(satom.getKind() == SEP_WAND);
        // nil does not occur in labels[0]
        Assert(!d_nil_ref.isNull());
        Node nrlem = nm->mkNode(SET_MEMBER, d_nil_ref, labels[0]).negate();
        Trace("sep-lemma")
            << "Sep::Lemma: sep.nil not in wand antecedant heap : " << nrlem
            << std::endl;
        d_im.lemma(nrlem, InferenceId::SEP_NIL_NOT_IN_HEAP);
        // make disjoint heap
        makeDisjointHeap(labels[1], {slbl, labels[0]});
      }
      conc = nm->mkNode(AND, children);
    }
    else if (satom.getKind() == SEP_PTO)
    {
      Node ss = nm->mkNode(SET_SINGLETON, satom[0]);
      if (slbl != ss)
      {
        conc = slbl.eqNode(ss);
      }
      // if we are not a part of the root label, we require applying downwards
      // closure, e.g. (SEP_LABEL (pto x y) A) =>
      // (or (SEP_LABEL (pto x y) B) (SEP_LABEL (pto x y) C)) where
      // A is the disjoint union of B and C.
      if (!sharesRootLabel(slbl, d_base_label))
      {
        std::map<Node, std::vector<Node> >::iterator itc =
            d_childrenMap.find(slbl);
        if (itc != d_childrenMap.end())
        {
          std::vector<Node> disjs;
          for (const Node& c : itc->second)
          {
            disjs.push_back(nm->mkNode(SEP_LABEL, satom, c));
          }
          Node conc2 = nm->mkNode(OR, disjs);
          conc = conc.isNull() ? conc2 : nm->mkNode(AND, conc, conc2);
        }
      }
      // note semantics of sep.nil is enforced globally
    }
    else if (satom.getKind() == SEP_EMP)
    {
      Node lem;
      Node emp_s = nm->mkConst(EmptySet(slbl.getType()));
      if (polarity)
      {
        lem = nm->mkNode(OR, fact.negate(), slbl.eqNode(emp_s));
      }
      else
      {
        Assert(!d_type_ref.isNull());
        Node kl = sm->mkDummySkolem("loc", d_type_ref);
        Node kd = sm->mkDummySkolem("data", d_type_data);
        Node econc = nm->mkNode(
            SEP_LABEL,
            nm->mkNode(SEP_STAR, nm->mkNode(SEP_PTO, kl, kd), d_true),
            slbl);
        // Node econc = nm->mkNode( AND, slbl.eqNode( emp_s ).negate(),
        lem = nm->mkNode(OR, fact.negate(), econc);
      }
      Trace("sep-lemma") << "Sep::Lemma : emp : " << lem << std::endl;
      d_im.lemma(lem, InferenceId::SEP_EMP);
    }
    else
    {
      // labeled emp should be rewritten
      Unreachable();
    }
    d_red_conc[slbl][satom] = conc;
  }
  if (conc.isNull())
  {
    Trace("sep-lemma-debug")
        << "Trivial conclusion, do not add lemma." << std::endl;
    return;
  }
  bool use_polarity = satom.getKind() == SEP_WAND ? !polarity : polarity;
  if (!use_polarity)
  {
    // introduce guard, assert positive version
    Trace("sep-lemma-debug")
        << "Negated spatial constraint asserted to sep theory: " << fact
        << std::endl;
    Node g = sm->mkDummySkolem("G", nm->booleanType());
    d_neg_guard_strategy[g].reset(new DecisionStrategySingleton(
        d_env, "sep_neg_guard", g, getValuation()));
    DecisionStrategySingleton* ds = d_neg_guard_strategy[g].get();
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_SEP_NEG_GUARD, ds);
    Node lit = ds->getLiteral(0);
    d_neg_guard[slbl][satom] = lit;
    Trace("sep-lemma-debug")
        << "Neg guard : " << slbl << " " << satom << " " << lit << std::endl;
    AlwaysAssert(!lit.isNull());
    d_neg_guards.push_back(lit);
    d_guard_to_assertion[lit] = satom;
    // Node lem = nm->mkNode( EQUAL, lit, conc );
    Node lem = nm->mkNode(OR, lit.negate(), conc);
    Trace("sep-lemma") << "Sep::Lemma : (neg) reduction : " << lem << std::endl;
    d_im.lemma(lem, InferenceId::SEP_NEG_REDUCTION);
  }
  else
  {
    // reduce based on implication
    Node lem = nm->mkNode(OR, fact.negate(), conc);
    Trace("sep-lemma") << "Sep::Lemma : reduction : " << lem << std::endl;
    d_im.lemma(lem, InferenceId::SEP_POS_REDUCTION);
  }
}

bool TheorySep::isSpatialKind(Kind k) const
{
  return k == SEP_STAR || k == SEP_WAND || k == SEP_PTO || k == SEP_EMP;
}

void TheorySep::postCheck(Effort level)
{
  if (level != EFFORT_LAST_CALL || d_state.isInConflict()
      || d_valuation.needCheck())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Trace("sep-process") << "Checking heap at full effort..." << std::endl;
  d_label_model.clear();
  d_tmodel.clear();
  d_pto_model.clear();
  Trace("sep-process") << "---Locations---" << std::endl;
  std::map<Node, int> min_id;
  for (const Node& t : d_type_references)
  {
    Trace("sep-process") << "  " << t << " = ";
    if (d_valuation.getModel()->hasTerm(t))
    {
      Node v = d_valuation.getModel()->getRepresentative(t);
      Trace("sep-process") << v << std::endl;
      // take minimal id
      std::map<Node, unsigned>::iterator itrc = d_type_ref_card_id.find(t);
      int tid = itrc == d_type_ref_card_id.end() ? -1 : (int)itrc->second;
      bool set_term_model;
      if (d_tmodel.find(v) == d_tmodel.end())
      {
        set_term_model = true;
      }
      else
      {
        set_term_model = min_id[v] > tid;
      }
      if (set_term_model)
      {
        d_tmodel[v] = t;
        min_id[v] = tid;
      }
    }
    else
    {
      Trace("sep-process") << "?" << std::endl;
    }
  }
  Trace("sep-process") << "---" << std::endl;
  // build positive/negative assertion lists for labels
  std::map<Node, bool> assert_active;
  // get the inactive assertions
  std::map<Node, std::vector<Node> > lbl_to_assertions;
  for (const Node& fact : d_spatial_assertions)
  {
    bool polarity = fact.getKind() != NOT;
    TNode atom = polarity ? fact : fact[0];
    Assert(atom.getKind() == SEP_LABEL);
    TNode satom = atom[0];
    TNode slbl = atom[1];
    lbl_to_assertions[slbl].push_back(fact);
    // check whether assertion is active : either polarity=true, or guard is not
    // asserted false
    assert_active[fact] = true;
    bool use_polarity = satom.getKind() == SEP_WAND ? !polarity : polarity;
    if (use_polarity)
    {
      if (satom.getKind() == SEP_PTO)
      {
        Node vv = d_valuation.getModel()->getRepresentative(satom[0]);
        if (d_pto_model.find(vv) == d_pto_model.end())
        {
          Trace("sep-process") << "Pto : " << satom[0] << " (" << vv << ") -> "
                               << satom[1] << std::endl;
          d_pto_model[vv] = satom[1];

          // replace this on pto-model since this term is more relevant
          Assert(vv.getType() == d_type_ref);
          if (std::find(
                  d_type_references.begin(), d_type_references.end(), satom[0])
              != d_type_references.end())
          {
            d_tmodel[vv] = satom[0];
          }
        }
      }
    }
    else
    {
      if (d_neg_guard[slbl].find(satom) != d_neg_guard[slbl].end())
      {
        // check if the guard is asserted positively
        Node guard = d_neg_guard[slbl][satom];
        bool value;
        if (getValuation().hasSatValue(guard, value))
        {
          assert_active[fact] = value;
        }
      }
    }
  }
  //(recursively) set inactive sub-assertions
  for (const Node& fact : d_spatial_assertions)
  {
    if (!assert_active[fact])
    {
      setInactiveAssertionRec(fact, lbl_to_assertions, assert_active);
    }
  }
  // set up model information based on active assertions
  for (const Node& fact : d_spatial_assertions)
  {
    bool polarity = fact.getKind() != NOT;
    TNode atom = polarity ? fact : fact[0];
    TNode satom = atom[0];
    TNode slbl = atom[1];
    if (assert_active[fact])
    {
      computeLabelModel(slbl);
    }
  }
  // debug print
  if (TraceIsOn("sep-process"))
  {
    Trace("sep-process") << "--- Current spatial assertions : " << std::endl;
    for (const Node& fact : d_spatial_assertions)
    {
      Trace("sep-process") << "  " << fact;
      if (!assert_active[fact])
      {
        Trace("sep-process") << " [inactive]";
      }
      Trace("sep-process") << std::endl;
    }
    Trace("sep-process") << "---" << std::endl;
  }
  if (TraceIsOn("sep-eqc"))
  {
    Trace("sep-eqc") << d_equalityEngine->debugPrintEqc();
  }

  bool addedLemma = false;
  bool needAddLemma = false;
  // check negated star / positive wand

  // get active labels
  std::map<Node, bool> active_lbl;
  if (options().sep.sepMinimalRefine)
  {
    for (const Node& fact : d_spatial_assertions)
    {
      bool polarity = fact.getKind() != NOT;
      TNode atom = polarity ? fact : fact[0];
      TNode satom = atom[0];
      bool use_polarity = satom.getKind() == SEP_WAND ? !polarity : polarity;
      if (!use_polarity)
      {
        Assert(assert_active.find(fact) != assert_active.end());
        if (assert_active[fact])
        {
          Assert(atom.getKind() == SEP_LABEL);
          TNode slbl = atom[1];
          std::map<Node, std::map<int, Node> >& lms = d_label_map[satom];
          if (lms.find(slbl) != lms.end())
          {
            Trace("sep-process-debug") << "Active lbl : " << slbl << std::endl;
            active_lbl[slbl] = true;
          }
        }
      }
    }
  }

  // process spatial assertions
  for (const Node& fact : d_spatial_assertions)
  {
    bool polarity = fact.getKind() != NOT;
    TNode atom = polarity ? fact : fact[0];
    TNode satom = atom[0];

    bool use_polarity = satom.getKind() == SEP_WAND ? !polarity : polarity;
    Trace("sep-process-debug") << "  check atom : " << satom << " use polarity "
                               << use_polarity << std::endl;
    if (use_polarity)
    {
      continue;
    }
    Assert(assert_active.find(fact) != assert_active.end());
    if (!assert_active[fact])
    {
      Trace("sep-process-debug")
          << "--> inactive negated assertion " << satom << std::endl;
      continue;
    }
    Assert(atom.getKind() == SEP_LABEL);
    TNode slbl = atom[1];
    Trace("sep-process") << "--> Active negated atom : " << satom
                         << ", lbl = " << slbl << std::endl;
    // add refinement lemma
    if (!ContainsKey(d_label_map[satom], slbl))
    {
      Trace("sep-process-debug") << "  no children." << std::endl;
      Assert(satom.getKind() == SEP_PTO || satom.getKind() == SEP_EMP);
      continue;
    }
    needAddLemma = true;
    Assert(!d_type_ref.isNull());
    TypeNode tn = nm->mkSetType(d_type_ref);
    // tn = nm->mkSetType(nm->mkRefType(tn));
    Node o_b_lbl_mval = d_label_model[slbl].getValue(tn);
    Trace("sep-process") << "    Model for " << slbl << " : " << o_b_lbl_mval
                         << std::endl;

    // get model values
    std::map<int, Node> mvals;
    for (const std::pair<const int, Node>& sub_element :
         d_label_map[satom][slbl])
    {
      int sub_index = sub_element.first;
      Node sub_lbl = sub_element.second;
      computeLabelModel(sub_lbl);
      Node lbl_mval = d_label_model[sub_lbl].getValue(tn);
      Trace("sep-process-debug") << "  child " << sub_index << " : " << sub_lbl
                                 << ", mval = " << lbl_mval << std::endl;
      mvals[sub_index] = lbl_mval;
    }

    // Now, assert model-instantiated implication based on the negation
    Assert(d_label_model.find(slbl) != d_label_model.end());
    std::vector<Node> conc;
    bool inst_success = true;
    // new refinement
    // instantiate the label
    std::map<Node, Node> visited;
    Node inst = instantiateLabel(
        satom, slbl, slbl, o_b_lbl_mval, visited, d_pto_model, tn, active_lbl);
    Trace("sep-inst-debug") << "    applied inst : " << inst << std::endl;
    if (inst.isNull())
    {
      inst_success = false;
    }
    else
    {
      inst = rewrite(inst);
      if (inst == (polarity ? d_true : d_false))
      {
        inst_success = false;
      }
      conc.push_back(polarity ? inst : inst.negate());
    }
    if (!inst_success)
    {
      continue;
    }
    std::vector<Node> lemc;
    Node pol_atom = atom;
    if (polarity)
    {
      pol_atom = atom.negate();
    }
    lemc.push_back(pol_atom);
    lemc.insert(lemc.end(), conc.begin(), conc.end());
    Node lem = nm->mkNode(OR, lemc);
    std::vector<Node>& rlems = d_refinement_lem[satom][slbl];
    if (std::find(rlems.begin(), rlems.end(), lem) == rlems.end())
    {
      rlems.push_back(lem);
      Trace("sep-process") << "-----> refinement lemma (#" << rlems.size()
                           << ") : " << lem << std::endl;
      Trace("sep-lemma") << "Sep::Lemma : negated star/wand refinement : "
                         << lem << std::endl;
      d_im.lemma(lem, InferenceId::SEP_REFINEMENT);
      addedLemma = true;
    }
    else
    {
      // this typically should not happen, should never happen for complete
      // base theories
      Trace("sep-process") << "*** repeated refinement lemma : " << lem
                           << std::endl;
      Trace("sep-warn") << "TheorySep : WARNING : repeated refinement lemma : "
                        << lem << "!!!" << std::endl;
    }
  }
  Trace("sep-process") << "...finished check of negated assertions, addedLemma="
                       << addedLemma << ", needAddLemma=" << needAddLemma
                       << std::endl;

  if (addedLemma)
  {
    return;
  }
  // must witness finite data points-to
  // if the data type is finite
  if (d_env.isFiniteType(d_type_data))
  {
    computeLabelModel(d_base_label);
    Trace("sep-process-debug") << "Check heap data for " << d_type_data
                               << " -> " << d_type_data << std::endl;
    std::vector<Node>& hlmodel = d_label_model[d_base_label].d_heap_locs_model;
    for (size_t j = 0, hsize = hlmodel.size(); j < hsize; j++)
    {
      Assert(hlmodel[j].getKind() == SET_SINGLETON);
      Node l = hlmodel[j][0];
      Trace("sep-process-debug") << "  location : " << l << std::endl;
      if (!d_pto_model[l].isNull())
      {
        Trace("sep-process-debug")
            << "  points-to data witness : " << d_pto_model[l] << std::endl;
        continue;
      }
      needAddLemma = true;
      Node ll;
      std::map<Node, Node>::iterator itm = d_tmodel.find(l);
      if (itm != d_tmodel.end())
      {
        ll = itm->second;
      }
      // otherwise, could try to assign arbitrary skolem?
      if (!ll.isNull())
      {
        Trace("sep-process") << "Must witness label : " << ll
                             << ", data type is " << d_type_data << std::endl;
        Node dsk = sm->mkDummySkolem(
            "dsk", d_type_data, "pto-data for implicit location");
        // if location is in the heap, then something must point to it
        Node lem = nm->mkNode(
            IMPLIES,
            nm->mkNode(SET_MEMBER, ll, d_base_label),
            nm->mkNode(SEP_STAR, nm->mkNode(SEP_PTO, ll, dsk), d_true));
        Trace("sep-lemma") << "Sep::Lemma : witness finite data-pto : " << lem
                           << std::endl;
        d_im.lemma(lem, InferenceId::SEP_WITNESS_FINITE_DATA);
        addedLemma = true;
      }
      else
      {
        // This should only happen if we are in an unbounded fragment
        Trace("sep-warn")
            << "TheorySep : WARNING : no term corresponding to location " << l
            << " in heap!!!" << std::endl;
      }
    }
  }

  if (addedLemma)
  {
    return;
  }

  if (needAddLemma)
  {
    d_im.setModelUnsound(IncompleteId::SEP);
  }
  Trace("sep-check") << "Sep::check(): " << level
                     << " done, conflict=" << d_state.isInConflict()
                     << std::endl;
}

bool TheorySep::needsCheckLastEffort() {
  return hasFacts();
}

void TheorySep::conflict(TNode a, TNode b) {
  Trace("sep-conflict") << "Sep::conflict : " << a << " " << b << std::endl;
  d_im.conflictEqConstantMerge(a, b);
}

TheorySep::HeapAssertInfo::HeapAssertInfo(context::Context* c)
    : d_posPto(c), d_negPto(c)
{
}

TheorySep::HeapAssertInfo * TheorySep::getOrMakeEqcInfo( Node n, bool doMake ) {
  std::map< Node, HeapAssertInfo* >::iterator e_i = d_eqc_info.find( n );
  if( e_i==d_eqc_info.end() ){
    if( doMake ){
      HeapAssertInfo* ei = new HeapAssertInfo(context());
      d_eqc_info[n] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*e_i).second;
  }
}

// Must process assertions at preprocess so that quantified assertions are
// processed properly.
void TheorySep::ppNotifyAssertions(const std::vector<Node>& assertions) {
  std::map<int, std::map<Node, size_t> > visited;
  std::map<int, std::map<Node, std::vector<Node> > > references;
  std::map<int, std::map<Node, bool> > references_strict;
  for (unsigned i = 0; i < assertions.size(); i++) {
    Trace("sep-pp") << "Process assertion : " << assertions[i] << std::endl;
    processAssertion(assertions[i], visited, references, references_strict,
                     true, true, false);
  }
}

//return cardinality
size_t TheorySep::processAssertion(
    Node n,
    std::map<int, std::map<Node, size_t> >& visited,
    std::map<int, std::map<Node, std::vector<Node> > >& references,
    std::map<int, std::map<Node, bool> >& references_strict,
    bool pol,
    bool hasPol,
    bool underSpatial)
{
  int index = hasPol ? ( pol ? 1 : -1 ) : 0;
  size_t card = 0;
  std::map<Node, size_t>::iterator it = visited[index].find(n);
  if( it==visited[index].end() ){
    Trace("sep-pp-debug") << "process assertion : " << n << ", index = " << index << std::endl;
    if (n.getKind() == SEP_EMP)
    {
      ensureHeapTypesFor(n);
      if( hasPol && pol ){
        references[index][n].clear();
        references_strict[index][n] = true;
      }else{
        card = 1;
      }
    }
    else if (n.getKind() == SEP_PTO)
    {
      ensureHeapTypesFor(n);
      if( quantifiers::TermUtil::hasBoundVarAttr( n[0] ) ){
        Assert(n[0].getType() == d_type_ref);
        if (d_bound_kind != bound_strict && d_bound_kind != bound_invalid)
        {
          d_bound_kind = bound_invalid;
          Trace("sep-bound")
              << "reference cannot be bound (due to quantified pto)."
              << std::endl;
        }
      }else{
        references[index][n].push_back( n[0] );
      }
      if( hasPol && pol ){
        references_strict[index][n] = true;
      }else{
        card = 1;
      }
    }else{
      bool isSpatial = n.getKind() == SEP_WAND || n.getKind() == SEP_STAR;
      bool newUnderSpatial = underSpatial || isSpatial;
      bool refStrict = isSpatial;
      for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        bool newHasPol, newPol;
        QuantPhaseReq::getEntailPolarity( n, i, hasPol, pol, newHasPol, newPol );
        int newIndex = newHasPol ? ( newPol ? 1 : -1 ) : 0;
        size_t ccard = processAssertion(n[i],
                                        visited,
                                        references,
                                        references_strict,
                                        newPol,
                                        newHasPol,
                                        newUnderSpatial);
        //update cardinality
        if (n.getKind() == SEP_STAR)
        {
          card += ccard;
        }
        else if (n.getKind() == SEP_WAND)
        {
          if( i==1 ){
            card = ccard;
          }
        }else if( ccard>card ){
          card = ccard;
        }
        //track references if we are or below a spatial operator
        if( newUnderSpatial ){
          bool add = true;
          if( references_strict[newIndex].find( n[i] )!=references_strict[newIndex].end() ){
            if( !isSpatial ){
              if( references_strict[index].find( n )==references_strict[index].end() ){
                references_strict[index][n] = true;
              }else{
                add = false;
                //TODO: can derive static equality between sets
              }
            }
          }else{
            if( isSpatial ){
              refStrict = false;
            }
          }
          if( add ){
            for( unsigned j=0; j<references[newIndex][n[i]].size(); j++ ){
              if( std::find( references[index][n].begin(), references[index][n].end(), references[newIndex][n[i]][j] )==references[index][n].end() ){
                references[index][n].push_back( references[newIndex][n[i]][j] );
              }
            }
          }
        }
      }
      if( isSpatial && refStrict ){
        if (n.getKind() == SEP_WAND)
        {
          //TODO
        }else{
          Assert(n.getKind() == SEP_STAR && hasPol && pol);
          references_strict[index][n] = true;
        }
      }
    }
    visited[index][n] = card;
  }else{
    card = it->second;
  }

  if( !underSpatial && ( !references[index][n].empty() || card>0 ) ){
    Assert(!d_type_ref.isNull());
    // add references to overall type
    unsigned bt = d_bound_kind;
    bool add = true;
    if( references_strict[index].find( n )!=references_strict[index].end() ){
      Trace("sep-bound") << "Strict bound found based on " << n << ", index = " << index << std::endl;
      if( bt!=bound_strict ){
        d_bound_kind = bound_strict;
        d_card_max = card;
      }else{
        //TODO: derive static equality
        add = false;
      }
    }else{
      add = bt!=bound_strict;
    }
    for (const Node& r : references[index][n])
    {
      if (std::find(d_type_references.begin(), d_type_references.end(), r)
          == d_type_references.end())
      {
        d_type_references.push_back(r);
      }
    }
    if( add ){
      //add max cardinality
      if (card > d_card_max)
      {
        d_card_max = card;
      }
    }
  }
  return card;
}

void TheorySep::ensureHeapTypesFor(Node atom) const
{
  Assert(!atom.isNull());
  if (!d_type_ref.isNull() && !d_type_data.isNull())
  {
    if (atom.getKind() == SEP_PTO)
    {
      TypeNode tn1 = atom[0].getType();
      TypeNode tn2 = atom[1].getType();
      // already declared, ensure compatible
      if ((!tn1.isNull() && tn1 != d_type_ref)
          || (!tn2.isNull() && tn2 != d_type_data))
      {
        std::stringstream ss;
        ss << "ERROR: the separation logic heap type has already been set to "
           << d_type_ref << " -> " << d_type_data
           << " but we have a constraint that uses different heap types, "
              "offending atom is "
           << atom << " with associated heap type " << tn1 << " -> " << tn2
           << std::endl;
      }
    }
  }
  else
  {
    // if not declared yet, and we have a separation logic constraint, throw
    // an error.
    std::stringstream ss;
    // error, heap not declared
    ss << "ERROR: the type of the separation logic heap has not been declared "
          "(e.g. via a declare-heap command), and we have a separation logic "
          "constraint "
       << atom << std::endl;
    throw LogicException(ss.str());
  }
}

void TheorySep::initializeBounds() {
  if (d_bounds_init)
  {
    return;
  }
  Trace("sep-bound") << "Initialize sep bounds..." << std::endl;
  d_bounds_init = true;
  if (d_type_ref.isNull())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Trace("sep-bound") << "Initialize bounds for " << d_type_ref << "..."
                     << std::endl;
  size_t n_emp = 0;
  if (d_bound_kind != bound_invalid)
  {
    n_emp = d_card_max;
  }
  else if (d_type_references.empty())
  {
    // must include at least one constant TODO: remove?
    n_emp = 1;
  }
  Trace("sep-bound") << "Cardinality element size : " << d_card_max
                     << std::endl;
  Trace("sep-bound") << "Type reference size : " << d_type_references.size()
                     << std::endl;
  Trace("sep-bound") << "Constructing " << n_emp << " cardinality constants."
                     << std::endl;
  for (size_t r = 0; r < n_emp; r++)
  {
    Node e = sm->mkDummySkolem(
        "e", d_type_ref, "cardinality bound element for seplog");
    d_type_references_card.push_back(e);
    d_type_ref_card_id[e] = r;
  }
}

Node TheorySep::getBaseLabel()
{
  if (!d_base_label.isNull())
  {
    return d_base_label;
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  initializeBounds();
  Trace("sep") << "Make base label for " << d_type_ref << std::endl;
  std::stringstream ss;
  ss << "__Lb";
  TypeNode ltn = nm->mkSetType(d_type_ref);
  Node n_lbl = sm->mkDummySkolem(ss.str(), ltn, "base label");
  d_base_label = n_lbl;
  // make reference bound
  Trace("sep") << "Make reference bound label for " << d_type_ref << std::endl;
  std::stringstream ss2;
  ss2 << "__Lu";
  d_reference_bound = sm->mkDummySkolem(ss2.str(), ltn, "");

  // check whether monotonic (elements can be added to tn without effecting
  // satisfiability)
  bool tn_is_monotonic = true;
  if (d_type_ref.isUninterpretedSort())
  {
    // TODO: use monotonicity inference
    tn_is_monotonic = !logicInfo().isQuantified();
  }
  else
  {
    tn_is_monotonic = !d_env.isFiniteType(d_type_ref);
  }
  // add a reference type for maximum occurrences of empty in a constraint
  if (tn_is_monotonic)
  {
    for (const Node& e : d_type_references_card)
    {
      // ensure that it is distinct from all other references so far
      for (const Node& r : d_type_references)
      {
        Node eq = nm->mkNode(EQUAL, e, r);
        d_im.lemma(eq.negate(), InferenceId::SEP_DISTINCT_REF);
      }
      d_type_references.push_back(e);
    }
  }
  else
  {
    d_type_references.insert(d_type_references.end(),
                             d_type_references_card.begin(),
                             d_type_references_card.end());
  }

  if (d_bound_kind != bound_invalid)
  {
    // construct bound
    d_reference_bound_max = mkUnion(d_type_ref, d_type_references);
    Trace("sep-bound") << "overall bound for " << d_base_label << " : "
                       << d_reference_bound_max << std::endl;

    Node slem = nm->mkNode(SET_SUBSET, d_base_label, d_reference_bound_max);
    Trace("sep-lemma") << "Sep::Lemma: reference bound for " << d_type_ref
                       << " : " << slem << std::endl;
    d_im.lemma(slem, InferenceId::SEP_REF_BOUND);

    // symmetry breaking
    size_t trcSize = d_type_references_card.size();
    if (trcSize > 1)
    {
      std::map<size_t, Node> lit_mem_map;
      for (size_t i = 0; i < trcSize; i++)
      {
        lit_mem_map[i] = nm->mkNode(
            SET_MEMBER, d_type_references_card[i], d_reference_bound_max);
      }
      for (size_t i = 0; i < (trcSize - 1); i++)
      {
        std::vector<Node> children;
        for (size_t j = (i + 1); j < trcSize; j++)
        {
          children.push_back(lit_mem_map[j].negate());
        }
        if (!children.empty())
        {
          Node sym_lem = nm->mkAnd(children);
          sym_lem = nm->mkNode(IMPLIES, lit_mem_map[i].negate(), sym_lem);
          Trace("sep-lemma")
              << "Sep::Lemma: symmetry breaking lemma : " << sym_lem
              << std::endl;
          d_im.lemma(sym_lem, InferenceId::SEP_SYM_BREAK);
        }
      }
    }
  }

  // assert that nil ref is not in base label
  Assert(!d_nil_ref.isNull());
  Node nrlem = nm->mkNode(SET_MEMBER, d_nil_ref, n_lbl).negate();
  Trace("sep-lemma") << "Sep::Lemma: sep.nil not in base label " << d_type_ref
                     << " : " << nrlem << std::endl;
  d_im.lemma(nrlem, InferenceId::SEP_NIL_NOT_IN_HEAP);

  return n_lbl;
}

Node TheorySep::mkUnion( TypeNode tn, std::vector< Node >& locs ) {
  Node u;
  if( locs.empty() ){
    TypeNode ltn = NodeManager::currentNM()->mkSetType(tn);
    return NodeManager::currentNM()->mkConst(EmptySet(ltn));
  }else{
    for( unsigned i=0; i<locs.size(); i++ ){
      Node s = locs[i];
      Assert(!s.isNull());
      s = NodeManager::currentNM()->mkNode(SET_SINGLETON, s);
      if( u.isNull() ){
        u = s;
      }else{
        u = NodeManager::currentNM()->mkNode(SET_UNION, s, u);
      }
    }
    return u;
  }
}

Node TheorySep::getLabel( Node atom, int child, Node lbl ) {
  std::map< int, Node >::iterator it = d_label_map[atom][lbl].find( child );
  if( it==d_label_map[atom][lbl].end() ){
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Assert(!d_type_ref.isNull());
    std::stringstream ss;
    ss << "__Lc" << child;
    TypeNode ltn = NodeManager::currentNM()->mkSetType(d_type_ref);
    Node n_lbl = sm->mkDummySkolem(ss.str(), ltn, "sep label");
    d_label_map[atom][lbl][child] = n_lbl;
    return n_lbl;
  }else{
    return (*it).second;
  }
}

void TheorySep::makeDisjointHeap(Node parent, const std::vector<Node>& children)
{
  Trace("sep-debug") << "disjoint heap: " << parent << " for " << children
                     << std::endl;
  Assert(children.size() >= 2);
  if (!sharesRootLabel(parent, d_base_label))
  {
    Assert(d_childrenMap.find(parent) == d_childrenMap.end());
    d_childrenMap[parent] = children;
  }
  // remember parent relationships
  for (const Node& c : children)
  {
    Assert(c.getType() == parent.getType());
    d_parentMap[c].push_back(parent);
  }
  // make the disjointness constraints
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> lems;
  Node ulem = nm->mkNode(SET_UNION, children[0], children[1]);
  size_t lsize = children.size();
  for (size_t i = 2; i < lsize; i++)
  {
    ulem = nm->mkNode(SET_UNION, ulem, children[i]);
  }
  ulem = parent.eqNode(ulem);
  lems.push_back(ulem);
  Node empSet = nm->mkConst(EmptySet(parent.getType()));
  for (size_t i = 0; i < lsize; i++)
  {
    for (size_t j = (i + 1); j < lsize; j++)
    {
      Node s = nm->mkNode(SET_INTER, children[i], children[j]);
      Node ilem = s.eqNode(empSet);
      lems.push_back(ilem);
    }
  }
  // send out definitional lemmas for introduced sets
  for (const Node& clem : lems)
  {
    d_im.lemma(clem, InferenceId::SEP_LABEL_DEF);
  }
}

std::vector<Node> TheorySep::getRootLabels(Node p) const
{
  std::vector<Node> roots;
  std::unordered_set<Node> visited;
  std::unordered_set<Node>::iterator it;
  std::vector<Node> visit;
  std::map<Node, std::vector<Node> >::const_iterator itp;
  Node cur;
  visit.push_back(p);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      itp = d_parentMap.find(cur);
      if (itp == d_parentMap.end())
      {
        roots.push_back(cur);
      }
      else
      {
        visit.insert(visit.end(), itp->second.begin(), itp->second.end());
      }
    }
  } while (!visit.empty());
  return roots;
}

bool TheorySep::sharesRootLabel(Node p, Node q) const
{
  if (p == q)
  {
    return true;
  }
  std::vector<Node> rp = getRootLabels(p);
  std::vector<Node> rq = getRootLabels(q);
  for (const Node& r : rp)
  {
    if (std::find(rq.begin(), rq.end(), r) != rq.end())
    {
      return true;
    }
  }
  return false;
}

Node TheorySep::applyLabel( Node n, Node lbl, std::map< Node, Node >& visited ) {
  Assert(n.getKind() != SEP_LABEL);
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  std::map<Node, Node>::iterator it = visited.find(n);
  if (it != visited.end())
  {
    return it->second;
  }
  Node ret;
  if (k == SEP_STAR || k == SEP_WAND || k == SEP_PTO)
  {
    ret = nm->mkNode(SEP_LABEL, n, lbl);
  }
  else if (k == SEP_EMP)
  {
    // (SEP_LABEL sep.emp L) is the same as (= L set.empty)
    ret = lbl.eqNode(nm->mkConst(EmptySet(lbl.getType())));
  }
  else if (n.getType().isBoolean() && n.getNumChildren() > 0)
  {
    ret = n;
    std::vector<Node> children;
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool childChanged = false;
    for (const Node& nc : n)
    {
      Node aln = applyLabel(nc, lbl, visited);
      children.push_back(aln);
      childChanged = childChanged || aln != nc;
    }
    if (childChanged)
    {
      ret = nm->mkNode(n.getKind(), children);
    }
  }
  else
  {
    ret = n;
  }
  visited[n] = ret;
  return ret;
}

Node TheorySep::instantiateLabel(Node n,
                                 Node o_lbl,
                                 Node lbl,
                                 Node lbl_v,
                                 std::map<Node, Node>& visited,
                                 std::map<Node, Node>& pto_model,
                                 TypeNode rtn,
                                 std::map<Node, bool>& active_lbl,
                                 unsigned ind)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sep-inst-debug") << "Instantiate label " << n << " " << lbl << " " << lbl_v << std::endl;
  if (options().sep.sepMinimalRefine && lbl != o_lbl
      && active_lbl.find(lbl) != active_lbl.end())
  {
    Trace("sep-inst") << "...do not instantiate " << o_lbl << " since it has an active sublabel " << lbl << std::endl;
    return Node::null();
  }
  else
  {
    if( TraceIsOn("sep-inst") ){
      if (n.getKind() == SEP_STAR || n.getKind() == SEP_WAND
          || n.getKind() == SEP_PTO || n.getKind() == SEP_EMP)
      {
        for( unsigned j=0; j<ind; j++ ){ Trace("sep-inst") << "  "; }
        Trace("sep-inst") << n << "[" << lbl << "] :: " << lbl_v << std::endl;
      }
    }
    Assert(n.getKind() != SEP_LABEL);
    if (n.getKind() == SEP_STAR || n.getKind() == SEP_WAND)
    {
      if( lbl==o_lbl ){
        std::vector< Node > children;
        children.resize( n.getNumChildren() );
        Assert(d_label_map[n].find(lbl) != d_label_map[n].end());
        std::map< int, Node > mvals;
        for( std::map< int, Node >::iterator itl = d_label_map[n][lbl].begin(); itl != d_label_map[n][lbl].end(); ++itl ){
          Node sub_lbl = itl->second;
          int sub_index = itl->first;
          Assert(sub_index >= 0 && sub_index < (int)children.size());
          Trace("sep-inst-debug") << "Sublabel " << sub_index << " is " << sub_lbl << std::endl;
          Node lbl_mval;
          if (n.getKind() == SEP_WAND && sub_index == 1)
          {
            Assert(d_label_map[n][lbl].find(0) != d_label_map[n][lbl].end());
            Node sub_lbl_0 = d_label_map[n][lbl][0];
            computeLabelModel( sub_lbl_0 );
            Assert(d_label_model.find(sub_lbl_0) != d_label_model.end());
            lbl_mval = NodeManager::currentNM()->mkNode(
                SET_UNION, lbl, d_label_model[sub_lbl_0].getValue(rtn));
          }else{
            computeLabelModel( sub_lbl );
            Assert(d_label_model.find(sub_lbl) != d_label_model.end());
            lbl_mval = d_label_model[sub_lbl].getValue( rtn );
          }
          Trace("sep-inst-debug") << "Sublabel value is " << lbl_mval  << std::endl;
          mvals[sub_index] = lbl_mval;
          children[sub_index] = instantiateLabel( n[sub_index], o_lbl, sub_lbl, lbl_mval, visited, pto_model, rtn, active_lbl, ind+1 );
          if( children[sub_index].isNull() ){
            return Node::null();
          }
        }
        Node empSet = NodeManager::currentNM()->mkConst(EmptySet(rtn));
        if (n.getKind() == SEP_STAR)
        {
          //disjoint contraints
          std::vector< Node > conj;
          std::vector< Node > bchildren;
          bchildren.insert( bchildren.end(), children.begin(), children.end() );
          Node vsu;
          std::vector< Node > vs;
          for( std::map< int, Node >::iterator itl = d_label_map[n][lbl].begin(); itl != d_label_map[n][lbl].end(); ++itl ){
            Node sub_lbl = itl->second;
            Node lbl_mval = d_label_model[sub_lbl].getValue( rtn );
            for( unsigned j=0; j<vs.size(); j++ ){
              bchildren.push_back(NodeManager::currentNM()
                                      ->mkNode(SET_INTER, lbl_mval, vs[j])
                                      .eqNode(empSet));
            }
            vs.push_back( lbl_mval );
            if( vsu.isNull() ){
              vsu = lbl_mval;
            }else{
              vsu = NodeManager::currentNM()->mkNode(SET_UNION, vsu, lbl_mval);
            }
          }
          bchildren.push_back( vsu.eqNode( lbl ) );

          Assert(bchildren.size() > 1);
          conj.push_back(NodeManager::currentNM()->mkNode(AND, bchildren));
          return NodeManager::currentNM()->mkOr(conj);
        }else{
          std::vector< Node > wchildren;
          //disjoint constraints
          Node sub_lbl_0 = d_label_map[n][lbl][0];
          Node lbl_mval_0 = d_label_model[sub_lbl_0].getValue( rtn );
          wchildren.push_back(NodeManager::currentNM()
                                  ->mkNode(SET_INTER, lbl_mval_0, lbl)
                                  .eqNode(empSet)
                                  .negate());

          //return the lemma
          wchildren.push_back( children[0].negate() );
          wchildren.push_back( children[1] );
          return NodeManager::currentNM()->mkNode(OR, wchildren);
        }
      }else{
        //nested star/wand, label it and return
        return NodeManager::currentNM()->mkNode(SEP_LABEL, n, lbl_v);
      }
    }
    else if (n.getKind() == SEP_PTO)
    {
      //check if this pto reference is in the base label, if not, then it does not need to be added as an assumption
      Assert(d_label_model.find(o_lbl) != d_label_model.end());
      Node vr = d_valuation.getModel()->getRepresentative( n[0] );
      Node svr = nm->mkNode(SET_SINGLETON, vr);
      bool inBaseHeap = std::find( d_label_model[o_lbl].d_heap_locs_model.begin(), d_label_model[o_lbl].d_heap_locs_model.end(), svr )!=d_label_model[o_lbl].d_heap_locs_model.end();
      Trace("sep-inst-debug") << "Is in base (non-instantiating) heap : " << inBaseHeap << " for value ref " << vr << " in " << o_lbl << std::endl;
      std::vector< Node > children;
      if( inBaseHeap ){
        Node s = nm->mkNode(SET_SINGLETON, n[0]);
        children.push_back(NodeManager::currentNM()->mkNode(
            SEP_LABEL,
            NodeManager::currentNM()->mkNode(SEP_PTO, n[0], n[1]),
            s));
      }else{
        //look up value of data
        std::map< Node, Node >::iterator it = pto_model.find( vr );
        if( it!=pto_model.end() ){
          if( n[1]!=it->second ){
            children.push_back(nm->mkNode(EQUAL, n[1], it->second));
          }
        }else{
          Trace("sep-inst-debug") << "Data for " << vr << " was not specified, do not add condition." << std::endl;
        }
      }
      Node singleton = nm->mkNode(SET_SINGLETON, n[0]);
      children.push_back(singleton.eqNode(lbl_v));
      Node ret = nm->mkAnd(children);
      Trace("sep-inst-debug") << "Return " << ret << std::endl;
      return ret;
    }
    else if (n.getKind() == SEP_EMP)
    {
      return lbl_v.eqNode(
          NodeManager::currentNM()->mkConst(EmptySet(lbl_v.getType())));
    }else{
      std::map< Node, Node >::iterator it = visited.find( n );
      if( it==visited.end() ){
        std::vector< Node > children;
        if (n.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.push_back( n.getOperator() );
        }
        bool childChanged = false;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node aln = instantiateLabel( n[i], o_lbl, lbl, lbl_v, visited, pto_model, rtn, active_lbl, ind );
          if( aln.isNull() ){
            return Node::null();
          }else{
            children.push_back( aln );
            childChanged = childChanged || aln!=n[i];
          }
        }
        Node ret = n;
        if( childChanged ){
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
        //careful about caching
        //visited[n] = ret;
        return ret;
      }else{
        return it->second;
      }
    }
  }
}

void TheorySep::setInactiveAssertionRec( Node fact, std::map< Node, std::vector< Node > >& lbl_to_assertions, std::map< Node, bool >& assert_active ) {
  Trace("sep-process-debug") << "setInactiveAssertionRec::inactive : " << fact << std::endl;
  assert_active[fact] = false;
  bool polarity = fact.getKind() != NOT;
  TNode atom = polarity ? fact : fact[0];
  TNode satom = atom[0];
  TNode slbl = atom[1];
  if (satom.getKind() == SEP_WAND || satom.getKind() == SEP_STAR)
  {
    for (size_t j = 0, nchild = satom.getNumChildren(); j < nchild; j++)
    {
      Node lblc = getLabel(satom, j, slbl);
      for( unsigned k=0; k<lbl_to_assertions[lblc].size(); k++ ){
        setInactiveAssertionRec( lbl_to_assertions[lblc][k], lbl_to_assertions, assert_active );
      }
    }
  }
}

void TheorySep::getLabelChildren(Node satom,
                                 Node lbl,
                                 std::vector<Node>& children,
                                 std::vector<Node>& labels)
{
  for (size_t i = 0, nchild = satom.getNumChildren(); i < nchild; i++)
  {
    Node lblc = getLabel(satom, i, lbl);
    Assert(!lblc.isNull());
    std::map< Node, Node > visited;
    Node lc = applyLabel(satom[i], lblc, visited);
    Assert(!lc.isNull());
    if (i == 1 && satom.getKind() == SEP_WAND)
    {
      lc = lc.negate();
    }
    children.push_back( lc );
    labels.push_back( lblc );
  }
  Assert(children.size() > 1);
}

void TheorySep::computeLabelModel( Node lbl ) {
  if (d_label_model[lbl].d_computed)
  {
    return;
  }
  d_label_model[lbl].d_computed = true;
  NodeManager* nm = NodeManager::currentNM();
  // we must get the value of lbl from the model: this is being run at last
  // call, after the model is constructed Assert(...); TODO
  Node v_val = d_valuation.getModel()->getRepresentative(lbl);
  Trace("sep-process") << "Model value (from valuation) for " << lbl << " : "
                       << v_val << std::endl;
  if (v_val.getKind() != SET_EMPTY)
  {
    while (v_val.getKind() == SET_UNION)
    {
      Assert(v_val[0].getKind() == SET_SINGLETON);
      d_label_model[lbl].d_heap_locs_model.push_back(v_val[0]);
      v_val = v_val[1];
    }
    if (v_val.getKind() == SET_SINGLETON)
    {
      d_label_model[lbl].d_heap_locs_model.push_back(v_val);
    }
    else
    {
      throw Exception("Could not establish value of heap in model.");
      Assert(false);
    }
  }
  for (const Node& s : d_label_model[lbl].d_heap_locs_model)
  {
    Assert(s.getKind() == SET_SINGLETON);
    Node u = s[0];
    Node tt;
    std::map<Node, Node>::iterator itm = d_tmodel.find(u);
    if (itm == d_tmodel.end())
    {
      TypeNode tn = u.getType();
      Trace("sep-process")
          << "WARNING: could not find symbolic term in model for " << u
          << ", cref type " << tn << std::endl;
      Assert(!d_type_references.empty());
      tt = d_type_references[0];
    }
    else
    {
      tt = itm->second;
    }
    Node stt = nm->mkNode(SET_SINGLETON, tt);
    Trace("sep-process-debug") << "...model : add " << tt << " for " << u
                               << " in lbl " << lbl << std::endl;
    d_label_model[lbl].d_heap_locs.push_back(stt);
  }
}

Node TheorySep::getRepresentative( Node t ) {
  if (d_equalityEngine->hasTerm(t))
  {
    return d_equalityEngine->getRepresentative(t);
  }else{
    return t;
  }
}

bool TheorySep::hasTerm(Node a) { return d_equalityEngine->hasTerm(a); }

bool TheorySep::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine->areEqual(a, b);
  }else{
    return false;
  }
}

bool TheorySep::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    if (d_equalityEngine->areDisequal(a, b, false))
    {
      return true;
    }
  }
  return false;
}

void TheorySep::eqNotifyMerge(TNode t1, TNode t2)
{
  HeapAssertInfo * e2 = getOrMakeEqcInfo( t2, false );
  if (!e2 || (e2->d_posPto.empty() && e2->d_negPto.empty()))
  {
    return;
  }
  // allocate the heap assert info for e1
  HeapAssertInfo* e1 = getOrMakeEqcInfo(t1, true);
  std::vector<Node> toAdd[2];
  for (size_t i = 0; i < 2; i++)
  {
    bool pol = i == 0;
    NodeList& e2list = pol ? e2->d_posPto : e2->d_negPto;
    for (const Node& p : e2list)
    {
      if (checkPto(e1, p, pol))
      {
        // add unless checkPto determined it was redundant
        toAdd[i].push_back(p);
      }
    }
  }
  // now that checks are complete, add them all now
  for (size_t i = 0; i < 2; i++)
  {
    NodeList& e1list = i == 0 ? e1->d_posPto : e1->d_negPto;
    for (const Node& p : toAdd[i])
    {
      e1list.push_back(p);
    }
  }
}

bool TheorySep::checkPto(HeapAssertInfo* e, Node p, bool polarity)
{
  Assert(e != nullptr);
  Assert(p.getKind() == SEP_LABEL && p[0].getKind() == SEP_PTO);
  NodeManager* nm = NodeManager::currentNM();
  Node plbl = p[1];
  Node pval = p[0][1];
  bool ret = true;
  // check for inferences involving p with all pto constraints already
  // contained in e.
  for (size_t i = 0; i < 2; i++)
  {
    bool pol = i == 0;
    NodeList& elist = pol ? e->d_posPto : e->d_negPto;
    for (const Node& q : elist)
    {
      Assert(q.getKind() == SEP_LABEL && q[0].getKind() == SEP_PTO);
      Node qlbl = q[1];
      Node qval = q[0][1];
      // We use instantiated labels where labels are set to singletons. We
      // assume these always share a root label.
      if (qlbl.getKind() != SET_SINGLETON && plbl.getKind() != SET_SINGLETON
          && !sharesRootLabel(plbl, qlbl))
      {
        Trace("sep-pto") << "Constraints " << p << " and " << q
                         << " do not share a root label" << std::endl;
        // if do not share a parent, skip
        continue;
      }
      if (polarity && pol)
      {
        // two positive pto
        if (!areEqual(pval, qval))
        {
          std::vector<Node> exp;
          if (plbl != qlbl)
          {
            // the labels are equal since we are tracking the sets of pto
            // constraints modulo equality on their labels
            Assert(areEqual(plbl, qlbl));
            exp.push_back(plbl.eqNode(qlbl));
          }
          exp.push_back(p);
          exp.push_back(q);
          // enforces injectiveness of pto
          //  (label (pto x y) A) ^ (label (pto z w) B) ^ A = B => y = w
          Node concn = pval.eqNode(qval);
          Trace("sep-pto") << "prop pos/pos: " << concn << " by " << exp
                           << std::endl;
          sendLemma(exp, concn, InferenceId::SEP_PTO_PROP);
          // Don't need to add this if the labels are identical. This is an
          // optimization to minimize the size of the pto list
          if (plbl == qlbl)
          {
            ret = false;
          }
        }
      }
      else if (polarity != pol)
      {
        // a positive and negative pto
        bool isSat = false;
        std::vector<Node> conc;
        // based on the lemma below, either the domain or range has to be
        // disequal. We iterate on each child of the pto
        for (size_t j = 0; j < 2; j++)
        {
          if (areDisequal(p[0][j], q[0][j]))
          {
            isSat = true;
            break;
          }
          if (p[0][j] != q[0][j])
          {
            conc.push_back(p[0][j].eqNode(q[0][j]).notNode());
          }
        }
        if (!isSat)
        {
          std::vector<Node> exp;
          if (plbl != qlbl)
          {
            // the labels are equal since we are tracking the sets of pto
            // constraints modulo equality on their labels
            Assert(areEqual(plbl, qlbl));
            exp.push_back(plbl.eqNode(qlbl));
          }
          Node pos = polarity ? p : q;
          Node neg = polarity ? q : p;
          exp.push_back(pos);
          exp.push_back(neg.notNode());
          Node concn = nm->mkOr(conc);
          Trace("sep-pto") << "prop neg/pos: " << concn << " by " << exp
                           << std::endl;
          // (label (pto x y) A) ^ ~(label (pto z w) B) ^ A = B =>
          // (x != z or y != w)
          sendLemma(exp, concn, InferenceId::SEP_PTO_NEG_PROP);
        }
      }
      else
      {
        // otherwise if both are disequal, do nothing
      }
    }
  }
  return ret;
}

void TheorySep::sendLemma( std::vector< Node >& ant, Node conc, InferenceId id, bool infer ) {
  Trace("sep-lemma-debug") << "Do rewrite on inference : " << conc << std::endl;
  conc = rewrite(conc);
  Trace("sep-lemma-debug") << "Got : " << conc << std::endl;
  if( conc!=d_true ){
    if( infer && conc!=d_false ){
      Node ant_n = NodeManager::currentNM()->mkAnd(ant);
      Trace("sep-lemma") << "Sep::Infer: " << conc << " from " << ant_n << " by " << id << std::endl;
      d_im.addPendingFact(conc, id, ant_n);
    }else{
      if( conc==d_false ){
        Trace("sep-lemma") << "Sep::Conflict: " << ant << " by " << id
                           << std::endl;
        d_im.conflictExp(id, PfRule::THEORY_INFERENCE, ant, {conc});
      }else{
        Trace("sep-lemma") << "Sep::Lemma: " << conc << " from " << ant
                           << " by " << id << std::endl;
        TrustNode trn =
            d_im.mkLemmaExp(conc, PfRule::THEORY_INFERENCE, ant, {}, {conc});
        d_im.addPendingLemma(
            trn.getNode(), id, LemmaProperty::NONE, trn.getGenerator());
      }
    }
  }
}

void TheorySep::doPending()
{
  d_im.doPendingFacts();
  d_im.doPendingLemmas();
}

Node TheorySep::HeapInfo::getValue( TypeNode tn ) {
  Assert(d_heap_locs.size() == d_heap_locs_model.size());
  if( d_heap_locs.empty() ){
    return NodeManager::currentNM()->mkConst(EmptySet(tn));
  }
  Node curr = d_heap_locs[0];
  for (unsigned j = 1; j < d_heap_locs.size(); j++)
  {
    curr = NodeManager::currentNM()->mkNode(SET_UNION, d_heap_locs[j], curr);
  }
  return curr;
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal
