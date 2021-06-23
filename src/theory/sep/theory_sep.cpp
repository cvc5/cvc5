/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace sep {

TheorySep::TheorySep(context::Context* c,
                     context::UserContext* u,
                     OutputChannel& out,
                     Valuation valuation,
                     const LogicInfo& logicInfo,
                     ProofNodeManager* pnm)
    : Theory(THEORY_SEP, c, u, out, valuation, logicInfo, pnm),
      d_lemmas_produced_c(u),
      d_bounds_init(false),
      d_state(c, u, valuation),
      d_im(*this, d_state, nullptr, "theory::sep::"),
      d_notify(*this),
      d_reduce(u),
      d_spatial_assertions(c)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // indicate we are using the default theory state object
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheorySep::~TheorySep() {
  for( std::map< Node, HeapAssertInfo * >::iterator it = d_eqc_info.begin(); it != d_eqc_info.end(); ++it ){
    delete it->second;
  }
}

void TheorySep::declareSepHeap(TypeNode locT, TypeNode dataT)
{
  if (!d_type_ref.isNull())
  {
    TypeNode te1 = d_loc_to_data_type.begin()->first;
    std::stringstream ss;
    ss << "ERROR: cannot declare heap types for separation logic more than "
          "once.  We are declaring heap of type ";
    ss << locT << " -> " << dataT << ", but we already have ";
    ss << d_type_ref << " -> " << d_type_data;
    throw LogicException(ss.str());
  }
  Node nullAtom;
  registerRefDataTypes(locT, dataT, nullAtom);
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
  d_equalityEngine->addFunctionKind(kind::SEP_PTO);
  // we could but don't do congruence on SEP_STAR here.
}

void TheorySep::preRegisterTerm(TNode n)
{
  Kind k = n.getKind();
  if (k == SEP_PTO || k == SEP_EMP || k == SEP_STAR || k == SEP_WAND)
  {
    registerRefDataTypesAtom(n);
  }
}

Node TheorySep::mkAnd( std::vector< TNode >& assumptions ) {
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}


/////////////////////////////////////////////////////////////////////////////
// T-PROPAGATION / REGISTRATION
/////////////////////////////////////////////////////////////////////////////

bool TheorySep::propagateLit(TNode literal)
{
  return d_im.propagateLit(literal);
}

TrustNode TheorySep::explain(TNode literal)
{
  Debug("sep") << "TheorySep::explain(" << literal << ")" << std::endl;
  return d_im.explainLit(literal);
}


/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////

void TheorySep::computeCareGraph() {
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


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

void TheorySep::postProcessModel( TheoryModel* m ){
  Trace("sep-model") << "Printing model for TheorySep..." << std::endl;

  std::vector< Node > sep_children;
  Node m_neq;
  Node m_heap;
  for( std::map< TypeNode, Node >::iterator it = d_base_label.begin(); it != d_base_label.end(); ++it ){
    //should only be constructing for one heap type
    Assert(m_heap.isNull());
    Assert(d_loc_to_data_type.find(it->first) != d_loc_to_data_type.end());
    Trace("sep-model") << "Model for heap, type = " << it->first << " with data type " << d_loc_to_data_type[it->first] << " : " << std::endl;
    TypeNode data_type = d_loc_to_data_type[it->first];
    computeLabelModel( it->second );
    if( d_label_model[it->second].d_heap_locs_model.empty() ){
      Trace("sep-model") << "  [empty]" << std::endl;
    }else{
      for( unsigned j=0; j<d_label_model[it->second].d_heap_locs_model.size(); j++ ){
        Assert(d_label_model[it->second].d_heap_locs_model[j].getKind()
               == kind::SINGLETON);
        std::vector< Node > pto_children;
        Node l = d_label_model[it->second].d_heap_locs_model[j][0];
        Assert(l.isConst());
        pto_children.push_back( l );
        Trace("sep-model") << " " << l << " -> ";
        if( d_pto_model[l].isNull() ){
          Trace("sep-model") << "_";
          //m->d_comment_str << "_";
          TypeEnumerator te_range( data_type );
          if (d_state.isFiniteType(data_type))
          {
            pto_children.push_back( *te_range );
          }else{
            //must enumerate until we find one that is not explicitly pointed to
            bool success = false;
            Node cv;
            do{
              cv = *te_range;
              if( std::find( d_heap_locs_nptos[l].begin(), d_heap_locs_nptos[l].end(), cv )==d_heap_locs_nptos[l].end() ){
                success = true;
              }else{
                ++te_range;
              }
            }while( !success );
            pto_children.push_back( cv );
          }
        }else{
          Trace("sep-model") << d_pto_model[l];
          Node vpto = d_valuation.getModel()->getRepresentative( d_pto_model[l] );
          Assert(vpto.isConst());
          pto_children.push_back( vpto );
        }
        Trace("sep-model") << std::endl;
        sep_children.push_back( NodeManager::currentNM()->mkNode( kind::SEP_PTO, pto_children ) );
      }
    }
    Node nil = getNilRef( it->first );
    Node vnil = d_valuation.getModel()->getRepresentative( nil );
    m_neq = NodeManager::currentNM()->mkNode( kind::EQUAL, nil, vnil );
    Trace("sep-model") << "sep.nil = " << vnil << std::endl;
    Trace("sep-model") << std::endl;
    if( sep_children.empty() ){
      TypeEnumerator te_domain( it->first );
      TypeEnumerator te_range( d_loc_to_data_type[it->first] );
      m_heap = NodeManager::currentNM()->mkNode( kind::SEP_EMP, *te_domain, *te_range );
    }else if( sep_children.size()==1 ){
      m_heap = sep_children[0];
    }else{
      m_heap = NodeManager::currentNM()->mkNode( kind::SEP_STAR, sep_children );
    }
    m->setHeapModel( m_heap, m_neq );
  }
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
  // assert to equality if non-spatial or a labelled pto
  if (!isSpatial || (!slbl.isNull() && satom.getKind() == SEP_PTO))
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
    HeapAssertInfo* ei = getOrMakeEqcInfo(r, true);
    addPto(ei, r, atom, polarity);
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
    TypeNode refType = getReferenceType(satom);
    Trace("sep-lemma-debug")
        << "...reference type is : " << refType << std::endl;
    Node b_lbl = getBaseLabel(refType);
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
      std::vector<Node> children;
      std::vector<Node> c_lems;
      TypeNode tn = getReferenceType(satom);
      if (d_reference_bound_max.find(tn) != d_reference_bound_max.end())
      {
        c_lems.push_back(nm->mkNode(SUBSET, slbl, d_reference_bound_max[tn]));
      }
      std::vector<Node> labels;
      getLabelChildren(satom, slbl, children, labels);
      Node empSet = nm->mkConst(EmptySet(slbl.getType()));
      Assert(children.size() > 1);
      if (satom.getKind() == SEP_STAR)
      {
        // reduction for heap : union, pairwise disjoint
        Node ulem = nm->mkNode(UNION, labels[0], labels[1]);
        size_t lsize = labels.size();
        for (size_t i = 2; i < lsize; i++)
        {
          ulem = nm->mkNode(UNION, ulem, labels[i]);
        }
        ulem = slbl.eqNode(ulem);
        Trace("sep-lemma-debug")
            << "Sep::Lemma : star reduction, union : " << ulem << std::endl;
        c_lems.push_back(ulem);
        for (size_t i = 0; i < lsize; i++)
        {
          for (size_t j = (i + 1); j < lsize; j++)
          {
            Node s = nm->mkNode(INTERSECTION, labels[i], labels[j]);
            Node ilem = s.eqNode(empSet);
            Trace("sep-lemma-debug")
                << "Sep::Lemma : star reduction, disjoint : " << ilem
                << std::endl;
            c_lems.push_back(ilem);
          }
        }
      }
      else
      {
        Node ulem = nm->mkNode(UNION, slbl, labels[0]);
        ulem = ulem.eqNode(labels[1]);
        Trace("sep-lemma-debug")
            << "Sep::Lemma : wand reduction, union : " << ulem << std::endl;
        c_lems.push_back(ulem);
        Node s = nm->mkNode(INTERSECTION, slbl, labels[0]);
        Node ilem = s.eqNode(empSet);
        Trace("sep-lemma-debug")
            << "Sep::Lemma : wand reduction, disjoint : " << ilem << std::endl;
        c_lems.push_back(ilem);
        // nil does not occur in labels[0]
        Node nr = getNilRef(tn);
        Node nrlem = nm->mkNode(MEMBER, nr, labels[0]).negate();
        Trace("sep-lemma")
            << "Sep::Lemma: sep.nil not in wand antecedant heap : " << nrlem
            << std::endl;
        d_im.lemma(nrlem, InferenceId::SEP_NIL_NOT_IN_HEAP);
      }
      // send out definitional lemmas for introduced sets
      for (const Node& clem : c_lems)
      {
        Trace("sep-lemma") << "Sep::Lemma : definition : " << clem << std::endl;
        d_im.lemma(clem, InferenceId::SEP_LABEL_DEF);
      }
      conc = nm->mkNode(AND, children);
    }
    else if (satom.getKind() == SEP_PTO)
    {
      // TODO(project##230): Find a safe type for the singleton operator
      Node ss = nm->mkSingleton(satom[0].getType(), satom[0]);
      if (slbl != ss)
      {
        conc = slbl.eqNode(ss);
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
        Node kl = sm->mkDummySkolem("loc", getReferenceType(satom));
        Node kd = sm->mkDummySkolem("data", getDataType(satom));
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
        "sep_neg_guard", g, getSatContext(), getValuation()));
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
  for (std::map<TypeNode, std::vector<Node> >::iterator itt =
           d_type_references_all.begin();
       itt != d_type_references_all.end();
       ++itt)
  {
    for (const Node& t : itt->second)
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
        }else{
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
  }
  Trace("sep-process") << "---" << std::endl;
  // build positive/negative assertion lists for labels
  std::map<Node, bool> assert_active;
  // get the inactive assertions
  std::map<Node, std::vector<Node> > lbl_to_assertions;
  for (NodeList::const_iterator i = d_spatial_assertions.begin();
       i != d_spatial_assertions.end();
       ++i)
  {
    Node fact = (*i);
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
          TypeNode vtn = vv.getType();
          if (std::find(d_type_references_all[vtn].begin(),
                        d_type_references_all[vtn].end(),
                        satom[0])
              != d_type_references_all[vtn].end())
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
  for (NodeList::const_iterator i = d_spatial_assertions.begin();
       i != d_spatial_assertions.end();
       ++i)
  {
    Node fact = (*i);
    if (!assert_active[fact])
    {
      setInactiveAssertionRec(fact, lbl_to_assertions, assert_active);
    }
  }
  // set up model information based on active assertions
  for (NodeList::const_iterator i = d_spatial_assertions.begin();
       i != d_spatial_assertions.end();
       ++i)
  {
    Node fact = (*i);
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
  if (Trace.isOn("sep-process"))
  {
    Trace("sep-process") << "--- Current spatial assertions : " << std::endl;
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      Trace("sep-process") << "  " << fact;
      if (!assert_active[fact])
      {
        Trace("sep-process") << " [inactive]";
      }
      Trace("sep-process") << std::endl;
    }
    Trace("sep-process") << "---" << std::endl;
  }
  if (Trace.isOn("sep-eqc"))
  {
    Trace("sep-eqc") << d_equalityEngine->debugPrintEqc();
  }

  bool addedLemma = false;
  bool needAddLemma = false;
  // check negated star / positive wand
  if (options::sepCheckNeg())
  {
    // get active labels
    std::map<Node, bool> active_lbl;
    if (options::sepMinimalRefine())
    {
      for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
        Node fact = (*i);
        bool polarity = fact.getKind() != NOT;
        TNode atom = polarity ? fact : fact[0];
        TNode satom = atom[0];
        bool use_polarity = satom.getKind() == SEP_WAND ? !polarity : polarity;
        if( !use_polarity ){
          Assert(assert_active.find(fact) != assert_active.end());
          if( assert_active[fact] ){
            Assert(atom.getKind() == SEP_LABEL);
            TNode slbl = atom[1];
            std::map<Node, std::map<int, Node> >& lms = d_label_map[satom];
            if (lms.find(slbl) != lms.end())
            {
              Trace("sep-process-debug")
                  << "Active lbl : " << slbl << std::endl;
              active_lbl[slbl] = true;
            }
          }
        }
      }
    }

    // process spatial assertions
    for (NodeList::const_iterator i = d_spatial_assertions.begin();
         i != d_spatial_assertions.end();
         ++i)
    {
      Node fact = (*i);
      bool polarity = fact.getKind() != NOT;
      TNode atom = polarity ? fact : fact[0];
      TNode satom = atom[0];

      bool use_polarity = satom.getKind() == SEP_WAND ? !polarity : polarity;
      Trace("sep-process-debug")
          << "  check atom : " << satom << " use polarity " << use_polarity
          << std::endl;
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
      TypeNode tn = getReferenceType(satom);
      tn = nm->mkSetType(tn);
      // tn = nm->mkSetType(nm->mkRefType(tn));
      Node o_b_lbl_mval = d_label_model[slbl].getValue(tn);
      Trace("sep-process") << "    Model for " << slbl << " : " << o_b_lbl_mval
                           << std::endl;

      // get model values
      std::map<int, Node> mvals;
      for (const std::pair<const int, Node>& sub_element : d_label_map[satom][slbl])
      {
        int sub_index = sub_element.first;
        Node sub_lbl = sub_element.second;
        computeLabelModel(sub_lbl);
        Node lbl_mval = d_label_model[sub_lbl].getValue(tn);
        Trace("sep-process-debug")
            << "  child " << sub_index << " : " << sub_lbl
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
      Node inst = instantiateLabel(satom,
                                   slbl,
                                   slbl,
                                   o_b_lbl_mval,
                                   visited,
                                   d_pto_model,
                                   tn,
                                   active_lbl);
      Trace("sep-inst-debug") << "    applied inst : " << inst << std::endl;
      if (inst.isNull())
      {
        inst_success = false;
      }
      else
      {
        inst = Rewriter::rewrite(inst);
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
        Trace("sep-process")
            << "*** repeated refinement lemma : " << lem << std::endl;
        Trace("sep-warn")
            << "TheorySep : WARNING : repeated refinement lemma : " << lem
            << "!!!" << std::endl;
      }
    }
    Trace("sep-process")
        << "...finished check of negated assertions, addedLemma=" << addedLemma
        << ", needAddLemma=" << needAddLemma << std::endl;
  }
  if (addedLemma)
  {
    return;
  }
  // must witness finite data points-to
  for (std::map<TypeNode, Node>::iterator it = d_base_label.begin();
       it != d_base_label.end();
       ++it)
  {
    TypeNode data_type = d_loc_to_data_type[it->first];
    // if the data type is finite
    if (!d_state.isFiniteType(data_type))
    {
      continue;
    }
    computeLabelModel(it->second);
    Trace("sep-process-debug") << "Check heap data for " << it->first << " -> "
                               << data_type << std::endl;
    std::vector<Node>& hlmodel = d_label_model[it->second].d_heap_locs_model;
    for (size_t j = 0, hsize = hlmodel.size(); j < hsize; j++)
    {
      Assert(hlmodel[j].getKind() == SINGLETON);
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
                             << ", data type is " << data_type << std::endl;
        Node dsk = sm->mkDummySkolem(
            "dsk", data_type, "pto-data for implicit location");
        // if location is in the heap, then something must point to it
        Node lem = nm->mkNode(
            IMPLIES,
            nm->mkNode(MEMBER, ll, it->second),
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
  // set up model
  Trace("sep-process-debug") << "...preparing sep model..." << std::endl;
  d_heap_locs_nptos.clear();
  // collect data points that are not pointed to
  for (context::CDList<Assertion>::const_iterator it = facts_begin();
       it != facts_end();
       ++it)
  {
    Node lit = (*it).d_assertion;
    if (lit.getKind() == NOT && lit[0].getKind() == SEP_PTO)
    {
      Node satom = lit[0];
      Node v1 = d_valuation.getModel()->getRepresentative(satom[0]);
      Node v2 = d_valuation.getModel()->getRepresentative(satom[1]);
      Trace("sep-process-debug")
          << v1 << " does not point-to " << v2 << std::endl;
      d_heap_locs_nptos[v1].push_back(v2);
    }
  }

  if (needAddLemma)
  {
    d_im.setIncomplete(IncompleteId::SEP);
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


TheorySep::HeapAssertInfo::HeapAssertInfo( context::Context* c ) : d_pto(c), d_has_neg_pto(c,false) {

}

TheorySep::HeapAssertInfo * TheorySep::getOrMakeEqcInfo( Node n, bool doMake ) {
  std::map< Node, HeapAssertInfo* >::iterator e_i = d_eqc_info.find( n );
  if( e_i==d_eqc_info.end() ){
    if( doMake ){
      HeapAssertInfo* ei = new HeapAssertInfo( getSatContext() );
      d_eqc_info[n] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*e_i).second;
  }
}

//for now, assume all constraints are for the same heap type (ensured by logic exceptions thrown in computeReferenceType2)
TypeNode TheorySep::getReferenceType( Node n ) {
  Assert(!d_type_ref.isNull());
  return d_type_ref;
}

TypeNode TheorySep::getDataType( Node n ) {
  Assert(!d_type_data.isNull());
  return d_type_data;
}

// Must process assertions at preprocess so that quantified assertions are
// processed properly.
void TheorySep::ppNotifyAssertions(const std::vector<Node>& assertions) {
  std::map<int, std::map<Node, int> > visited;
  std::map<int, std::map<Node, std::vector<Node> > > references;
  std::map<int, std::map<Node, bool> > references_strict;
  for (unsigned i = 0; i < assertions.size(); i++) {
    Trace("sep-pp") << "Process assertion : " << assertions[i] << std::endl;
    processAssertion(assertions[i], visited, references, references_strict,
                     true, true, false);
  }
  // if data type is unconstrained, assume a fresh uninterpreted sort
  if (!d_type_ref.isNull()) {
    if (d_type_data.isNull()) {
      d_type_data = NodeManager::currentNM()->mkSort("_sep_U");
      Trace("sep-type") << "Sep: assume data type " << d_type_data << std::endl;
      d_loc_to_data_type[d_type_ref] = d_type_data;
    }
  }
}

//return cardinality
int TheorySep::processAssertion(
    Node n,
    std::map<int, std::map<Node, int> >& visited,
    std::map<int, std::map<Node, std::vector<Node> > >& references,
    std::map<int, std::map<Node, bool> >& references_strict,
    bool pol,
    bool hasPol,
    bool underSpatial)
{
  int index = hasPol ? ( pol ? 1 : -1 ) : 0;
  int card = 0;
  std::map< Node, int >::iterator it = visited[index].find( n );
  if( it==visited[index].end() ){
    Trace("sep-pp-debug") << "process assertion : " << n << ", index = " << index << std::endl;
    if( n.getKind()==kind::SEP_EMP ){
      registerRefDataTypesAtom(n);
      if( hasPol && pol ){
        references[index][n].clear();
        references_strict[index][n] = true;
      }else{
        card = 1;
      }
    }else if( n.getKind()==kind::SEP_PTO ){
      registerRefDataTypesAtom(n);
      if( quantifiers::TermUtil::hasBoundVarAttr( n[0] ) ){
        TypeNode tn1 = n[0].getType();
        if( d_bound_kind[tn1]!=bound_strict && d_bound_kind[tn1]!=bound_invalid ){
          d_bound_kind[tn1] = bound_invalid;
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
      bool isSpatial = n.getKind()==kind::SEP_WAND || n.getKind()==kind::SEP_STAR;
      bool newUnderSpatial = underSpatial || isSpatial;
      bool refStrict = isSpatial;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bool newHasPol, newPol;
        QuantPhaseReq::getEntailPolarity( n, i, hasPol, pol, newHasPol, newPol );
        int newIndex = newHasPol ? ( newPol ? 1 : -1 ) : 0;
        int ccard = processAssertion( n[i], visited, references, references_strict, newPol, newHasPol, newUnderSpatial );
        //update cardinality
        if( n.getKind()==kind::SEP_STAR ){
          card += ccard;
        }else if( n.getKind()==kind::SEP_WAND ){
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
        if( n.getKind()==kind::SEP_WAND ){
          //TODO
        }else{
          Assert(n.getKind() == kind::SEP_STAR && hasPol && pol);
          references_strict[index][n] = true;
        }
      }
    }
    visited[index][n] = card;
  }else{
    card = it->second;
  }

  if( !underSpatial && ( !references[index][n].empty() || card>0 ) ){
    TypeNode tn = getReferenceType( n );
    Assert(!tn.isNull());
    // add references to overall type
    unsigned bt = d_bound_kind[tn];
    bool add = true;
    if( references_strict[index].find( n )!=references_strict[index].end() ){
      Trace("sep-bound") << "Strict bound found based on " << n << ", index = " << index << std::endl;
      if( bt!=bound_strict ){
        d_bound_kind[tn] = bound_strict;
        //d_type_references[tn].clear();
        d_card_max[tn] = card;
      }else{
        //TODO: derive static equality
        add = false;
      }
    }else{
      add = bt!=bound_strict;
    }
    for( unsigned i=0; i<references[index][n].size(); i++ ){
      if( std::find( d_type_references[tn].begin(), d_type_references[tn].end(), references[index][n][i] )==d_type_references[tn].end() ){
        d_type_references[tn].push_back( references[index][n][i] );
      }
    }
    if( add ){
      //add max cardinality
      if( card>(int)d_card_max[tn] ){
        d_card_max[tn] = card;
      }
    }
  }
  return card;
}

void TheorySep::registerRefDataTypesAtom(Node atom)
{
  TypeNode tn1;
  TypeNode tn2;
  Kind k = atom.getKind();
  if (k == SEP_PTO || k == SEP_EMP)
  {
    tn1 = atom[0].getType();
    tn2 = atom[1].getType();
  }
  else
  {
    Assert(k == SEP_STAR || k == SEP_WAND);
  }
  registerRefDataTypes(tn1, tn2, atom);
}

void TheorySep::registerRefDataTypes(TypeNode tn1, TypeNode tn2, Node atom)
{
  if (!d_type_ref.isNull())
  {
    Assert(!atom.isNull());
    // already declared, ensure compatible
    if ((!tn1.isNull() && !tn1.isComparableTo(d_type_ref))
        || (!tn2.isNull() && !tn2.isComparableTo(d_type_data)))
    {
      std::stringstream ss;
      ss << "ERROR: the separation logic heap type has already been set to "
         << d_type_ref << " -> " << d_type_data
         << " but we have a constraint that uses different heap types, "
            "offending atom is "
         << atom << " with associated heap type " << tn1 << " -> " << tn2
         << std::endl;
    }
    return;
  }
  // if not declared yet, and we have a separation logic constraint, throw
  // an error.
  if (!atom.isNull())
  {
    std::stringstream ss;
    // error, heap not declared
    ss << "ERROR: the type of the separation logic heap has not been declared "
          "(e.g. via a declare-heap command), and we have a separation logic "
          "constraint "
       << atom << std::endl;
    throw LogicException(ss.str());
  }
  // otherwise set it
  Trace("sep-type") << "Sep: assume location type " << tn1
                    << " is associated with data type " << tn2 << std::endl;
  d_loc_to_data_type[tn1] = tn2;
  // for now, we only allow heap constraints of one type
  d_type_ref = tn1;
  d_type_data = tn2;
  d_bound_kind[tn1] = bound_default;
}

void TheorySep::initializeBounds() {
  if( !d_bounds_init ){
    Trace("sep-bound")  << "Initialize sep bounds..." << std::endl;
    d_bounds_init = true;
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    for( std::map< TypeNode, TypeNode >::iterator it = d_loc_to_data_type.begin(); it != d_loc_to_data_type.end(); ++it ){
      TypeNode tn = it->first;
      Trace("sep-bound")  << "Initialize bounds for " << tn << "..." << std::endl;
      unsigned n_emp = 0;
      if( d_bound_kind[tn] != bound_invalid ){
        n_emp = d_card_max[tn];
      }else if( d_type_references[tn].empty() ){
        //must include at least one constant TODO: remove?
        n_emp = 1;
      }
      Trace("sep-bound") << "Cardinality element size : " << d_card_max[tn] << std::endl;
      Trace("sep-bound") << "Type reference size : " << d_type_references[tn].size() << std::endl;
      Trace("sep-bound") << "Constructing " << n_emp << " cardinality constants." << std::endl;
      for( unsigned r=0; r<n_emp; r++ ){
        Node e =
            sm->mkDummySkolem("e", tn, "cardinality bound element for seplog");
        d_type_references_card[tn].push_back( e );
        d_type_ref_card_id[e] = r;
      }
    }
  }
}

Node TheorySep::getBaseLabel( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_base_label.find( tn );
  if( it==d_base_label.end() ){
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    initializeBounds();
    Trace("sep") << "Make base label for " << tn << std::endl;
    std::stringstream ss;
    ss << "__Lb";
    TypeNode ltn = nm->mkSetType(tn);
    Node n_lbl = sm->mkDummySkolem(ss.str(), ltn, "base label");
    d_base_label[tn] = n_lbl;
    //make reference bound
    Trace("sep") << "Make reference bound label for " << tn << std::endl;
    std::stringstream ss2;
    ss2 << "__Lu";
    d_reference_bound[tn] = sm->mkDummySkolem(ss2.str(), ltn, "");
    d_type_references_all[tn].insert( d_type_references_all[tn].end(), d_type_references[tn].begin(), d_type_references[tn].end() );

    //check whether monotonic (elements can be added to tn without effecting satisfiability)
    bool tn_is_monotonic = true;
    if( tn.isSort() ){
      //TODO: use monotonicity inference
      tn_is_monotonic = !getLogicInfo().isQuantified();
    }else{
      tn_is_monotonic = tn.getCardinality().isInfinite();
    }
    //add a reference type for maximum occurrences of empty in a constraint
    if( options::sepDisequalC() && tn_is_monotonic ){
      for( unsigned r=0; r<d_type_references_card[tn].size(); r++ ){
        Node e = d_type_references_card[tn][r];
        //ensure that it is distinct from all other references so far
        for( unsigned j=0; j<d_type_references_all[tn].size(); j++ ){
          Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, e, d_type_references_all[tn][j] );
          d_im.lemma(eq.negate(), InferenceId::SEP_DISTINCT_REF);
        }
        d_type_references_all[tn].push_back( e );
      }
    }else{
      //break symmetries TODO

      d_type_references_all[tn].insert( d_type_references_all[tn].end(), d_type_references_card[tn].begin(), d_type_references_card[tn].end() );
    }
    //Assert( !d_type_references_all[tn].empty() );

    if (d_bound_kind[tn] != bound_invalid)
    {
      //construct bound
      d_reference_bound_max[tn] = mkUnion( tn, d_type_references_all[tn] );
      Trace("sep-bound") << "overall bound for " << d_base_label[tn] << " : " << d_reference_bound_max[tn] << std::endl;

      Node slem = NodeManager::currentNM()->mkNode( kind::SUBSET, d_base_label[tn], d_reference_bound_max[tn] );
      Trace("sep-lemma") << "Sep::Lemma: reference bound for " << tn << " : " << slem << std::endl;
      d_im.lemma(slem, InferenceId::SEP_REF_BOUND);

      //symmetry breaking
      if( d_type_references_card[tn].size()>1 ){
        std::map< unsigned, Node > lit_mem_map;
        for( unsigned i=0; i<d_type_references_card[tn].size(); i++ ){
          lit_mem_map[i] = NodeManager::currentNM()->mkNode( kind::MEMBER, d_type_references_card[tn][i], d_reference_bound_max[tn]);
        }
        for( unsigned i=0; i<(d_type_references_card[tn].size()-1); i++ ){
          std::vector< Node > children;
          for( unsigned j=(i+1); j<d_type_references_card[tn].size(); j++ ){
            children.push_back( lit_mem_map[j].negate() );
          }
          if( !children.empty() ){
            Node sym_lem = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::AND, children );
            sym_lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, lit_mem_map[i].negate(), sym_lem );
            Trace("sep-lemma") << "Sep::Lemma: symmetry breaking lemma : " << sym_lem << std::endl;
            d_im.lemma(sym_lem, InferenceId::SEP_SYM_BREAK);
          }
        }
      }
    }

    //assert that nil ref is not in base label
    Node nr = getNilRef( tn );
    Node nrlem = NodeManager::currentNM()->mkNode( kind::MEMBER, nr, n_lbl ).negate();
    Trace("sep-lemma") << "Sep::Lemma: sep.nil not in base label " << tn << " : " << nrlem << std::endl;
    d_im.lemma(nrlem, InferenceId::SEP_NIL_NOT_IN_HEAP);

    return n_lbl;
  }else{
    return it->second;
  }
}

Node TheorySep::getNilRef( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_nil_ref.find( tn );
  if( it==d_nil_ref.end() ){
    Node nil = NodeManager::currentNM()->mkNullaryOperator( tn, kind::SEP_NIL );
    setNilRef( tn, nil );
    return nil;
  }else{
    return it->second;
  }
}

void TheorySep::setNilRef( TypeNode tn, Node n ) {
  Assert(n.getType() == tn);
  d_nil_ref[tn] = n;
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
      s = NodeManager::currentNM()->mkSingleton(tn, s);
      if( u.isNull() ){
        u = s;
      }else{
        u = NodeManager::currentNM()->mkNode( kind::UNION, s, u );
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
    TypeNode refType = getReferenceType( atom );
    std::stringstream ss;
    ss << "__Lc" << child;
    TypeNode ltn = NodeManager::currentNM()->mkSetType(refType);
    //TypeNode ltn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(refType));
    Node n_lbl = sm->mkDummySkolem(ss.str(), ltn, "sep label");
    d_label_map[atom][lbl][child] = n_lbl;
    d_label_map_parent[n_lbl] = lbl;
    return n_lbl;
  }else{
    return (*it).second;
  }
}

Node TheorySep::applyLabel( Node n, Node lbl, std::map< Node, Node >& visited ) {
  Assert(n.getKind() != kind::SEP_LABEL);
  if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_WAND || n.getKind()==kind::SEP_PTO || n.getKind()==kind::SEP_EMP ){
    return NodeManager::currentNM()->mkNode( kind::SEP_LABEL, n, lbl );
  }else if( !n.getType().isBoolean() || n.getNumChildren()==0 ){
    return n;
  }else{
    std::map< Node, Node >::iterator it = visited.find( n );
    if( it==visited.end() ){
      std::vector< Node > children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node aln = applyLabel( n[i], lbl, visited );
        children.push_back( aln );
        childChanged = childChanged || aln!=n[i];
      }
      Node ret = n;
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
      visited[n] = ret;
      return ret;
    }else{
      return it->second;
    }
  }
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
  Trace("sep-inst-debug") << "Instantiate label " << n << " " << lbl << " " << lbl_v << std::endl;
  if( options::sepMinimalRefine() && lbl!=o_lbl && active_lbl.find( lbl )!=active_lbl.end() ){
    Trace("sep-inst") << "...do not instantiate " << o_lbl << " since it has an active sublabel " << lbl << std::endl;
    return Node::null();
  }else{
    if( Trace.isOn("sep-inst") ){
      if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_WAND  || n.getKind()==kind::SEP_PTO || n.getKind()==kind::SEP_EMP ){
        for( unsigned j=0; j<ind; j++ ){ Trace("sep-inst") << "  "; }
        Trace("sep-inst") << n << "[" << lbl << "] :: " << lbl_v << std::endl;
      }
    }
    Assert(n.getKind() != kind::SEP_LABEL);
    if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_WAND ){
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
          if( n.getKind()==kind::SEP_WAND && sub_index==1 ){
            Assert(d_label_map[n][lbl].find(0) != d_label_map[n][lbl].end());
            Node sub_lbl_0 = d_label_map[n][lbl][0];
            computeLabelModel( sub_lbl_0 );
            Assert(d_label_model.find(sub_lbl_0) != d_label_model.end());
            lbl_mval = NodeManager::currentNM()->mkNode( kind::UNION, lbl, d_label_model[sub_lbl_0].getValue( rtn ) );
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
        if( n.getKind()==kind::SEP_STAR ){

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
              bchildren.push_back( NodeManager::currentNM()->mkNode( kind::INTERSECTION, lbl_mval, vs[j] ).eqNode( empSet ) );
            }
            vs.push_back( lbl_mval );
            if( vsu.isNull() ){
              vsu = lbl_mval;
            }else{
              vsu = NodeManager::currentNM()->mkNode( kind::UNION, vsu, lbl_mval );
            }
          }
          bchildren.push_back( vsu.eqNode( lbl ) );

          Assert(bchildren.size() > 1);
          conj.push_back( NodeManager::currentNM()->mkNode( kind::AND, bchildren ) );

          if( options::sepChildRefine() ){
            //child-specific refinements (TODO: use ?)
            for( unsigned i=0; i<children.size(); i++ ){
              std::vector< Node > tchildren;
              Node mval = mvals[i];
              tchildren.push_back(
                  NodeManager::currentNM()->mkNode(kind::SUBSET, mval, lbl));
              tchildren.push_back( children[i] );
              std::vector< Node > rem_children;
              for( unsigned j=0; j<children.size(); j++ ){
                if( j!=i ){
                  rem_children.push_back( n[j] );
                }
              }
              std::map< Node, Node > rvisited;
              Node rem = rem_children.size()==1 ? rem_children[0] : NodeManager::currentNM()->mkNode( kind::SEP_STAR, rem_children );
              rem = applyLabel( rem, NodeManager::currentNM()->mkNode( kind::SETMINUS, lbl, mval ), rvisited );
              tchildren.push_back( rem );
              conj.push_back( NodeManager::currentNM()->mkNode( kind::AND, tchildren ) );
            }
          }
          return conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( kind::OR, conj );
        }else{
          std::vector< Node > wchildren;
          //disjoint constraints
          Node sub_lbl_0 = d_label_map[n][lbl][0];
          Node lbl_mval_0 = d_label_model[sub_lbl_0].getValue( rtn );
          wchildren.push_back( NodeManager::currentNM()->mkNode( kind::INTERSECTION, lbl_mval_0, lbl ).eqNode( empSet ).negate() );

          //return the lemma
          wchildren.push_back( children[0].negate() );
          wchildren.push_back( children[1] );
          return NodeManager::currentNM()->mkNode( kind::OR, wchildren );
        }
      }else{
        //nested star/wand, label it and return
        return NodeManager::currentNM()->mkNode( kind::SEP_LABEL, n, lbl_v );
      }
    }else if( n.getKind()==kind::SEP_PTO ){
      //check if this pto reference is in the base label, if not, then it does not need to be added as an assumption
      Assert(d_label_model.find(o_lbl) != d_label_model.end());
      Node vr = d_valuation.getModel()->getRepresentative( n[0] );
      // TODO(project##230): Find a safe type for the singleton operator
      Node svr = NodeManager::currentNM()->mkSingleton(vr.getType(), vr);
      bool inBaseHeap = std::find( d_label_model[o_lbl].d_heap_locs_model.begin(), d_label_model[o_lbl].d_heap_locs_model.end(), svr )!=d_label_model[o_lbl].d_heap_locs_model.end();
      Trace("sep-inst-debug") << "Is in base (non-instantiating) heap : " << inBaseHeap << " for value ref " << vr << " in " << o_lbl << std::endl;
      std::vector< Node > children;
      if( inBaseHeap ){
        // TODO(project##230): Find a safe type for the singleton operator
        Node s = NodeManager::currentNM()->mkSingleton(n[0].getType(),  n[0]);
        children.push_back( NodeManager::currentNM()->mkNode( kind::SEP_LABEL, NodeManager::currentNM()->mkNode( kind::SEP_PTO, n[0], n[1] ), s ) );
      }else{
        //look up value of data
        std::map< Node, Node >::iterator it = pto_model.find( vr );
        if( it!=pto_model.end() ){
          if( n[1]!=it->second ){
            children.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n[1], it->second ) );
          }
        }else{
          Trace("sep-inst-debug") << "Data for " << vr << " was not specified, do not add condition." << std::endl;
        }
      }
      // TODO(project##230): Find a safe type for the singleton operator
      Node singleton = NodeManager::currentNM()->mkSingleton(n[0].getType(), n[0]);
      children.push_back(singleton.eqNode(lbl_v));
      Node ret = children.empty() ? NodeManager::currentNM()->mkConst( true ) : ( children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::AND, children ) );
      Trace("sep-inst-debug") << "Return " << ret << std::endl;
      return ret;
    }else if( n.getKind()==kind::SEP_EMP ){
      //return NodeManager::currentNM()->mkConst( lbl_v.getKind()==kind::EMPTYSET );
      return lbl_v.eqNode(
          NodeManager::currentNM()->mkConst(EmptySet(lbl_v.getType())));
    }else{
      std::map< Node, Node >::iterator it = visited.find( n );
      if( it==visited.end() ){
        std::vector< Node > children;
        if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
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
  bool polarity = fact.getKind() != kind::NOT;
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
  if( !d_label_model[lbl].d_computed ){
    d_label_model[lbl].d_computed = true;

    //we must get the value of lbl from the model: this is being run at last call, after the model is constructed
    //Assert(...); TODO
    Node v_val = d_valuation.getModel()->getRepresentative( lbl );
    Trace("sep-process") << "Model value (from valuation) for " << lbl << " : " << v_val << std::endl;
    if( v_val.getKind()!=kind::EMPTYSET ){
      while( v_val.getKind()==kind::UNION ){
        Assert(v_val[0].getKind() == kind::SINGLETON);
        d_label_model[lbl].d_heap_locs_model.push_back(v_val[0]);
        v_val = v_val[1];
      }
      if( v_val.getKind()==kind::SINGLETON ){
        d_label_model[lbl].d_heap_locs_model.push_back( v_val );
      }else{
        throw Exception("Could not establish value of heap in model.");
        Assert(false);
      }
    }
    for( unsigned j=0; j<d_label_model[lbl].d_heap_locs_model.size(); j++ ){
      Node u = d_label_model[lbl].d_heap_locs_model[j];
      Assert(u.getKind() == kind::SINGLETON);
      u = u[0];
      Node tt;
      std::map< Node, Node >::iterator itm = d_tmodel.find( u );
      if( itm==d_tmodel.end() ) {
        //Trace("sep-process") << "WARNING: could not find symbolic term in model for " << u << std::endl;
        //Assert( false );
        //tt = u;
        //TypeNode tn = u.getType().getRefConstituentType();
        TypeNode tn = u.getType();
        Trace("sep-process") << "WARNING: could not find symbolic term in model for " << u << ", cref type " << tn << std::endl;
        Assert(d_type_references_all.find(tn) != d_type_references_all.end());
        Assert(!d_type_references_all[tn].empty());
        tt = d_type_references_all[tn][0];
      }else{
        tt = itm->second;
      }
      // TODO(project##230): Find a safe type for the singleton operator
      Node stt = NodeManager::currentNM()->mkSingleton(tt.getType(), tt);
      Trace("sep-process-debug") << "...model : add " << tt << " for " << u << " in lbl " << lbl << std::endl;
      d_label_model[lbl].d_heap_locs.push_back( stt );
    }
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
  if( e2 && ( !e2->d_pto.get().isNull() || e2->d_has_neg_pto.get() ) ){
    HeapAssertInfo * e1 = getOrMakeEqcInfo( t1, true );
    if( !e2->d_pto.get().isNull() ){
      if( !e1->d_pto.get().isNull() ){
        Trace("sep-pto-debug") << "While merging " << t1 << " " << t2 << ", merge pto." << std::endl;
        mergePto( e1->d_pto.get(), e2->d_pto.get() );
      }else{
        e1->d_pto.set( e2->d_pto.get() );
      }
    }
    e1->d_has_neg_pto.set( e1->d_has_neg_pto.get() || e2->d_has_neg_pto.get() );
    //validate
    validatePto( e1, t1 );
  }
}

void TheorySep::validatePto( HeapAssertInfo * ei, Node ei_n ) {
  if( !ei->d_pto.get().isNull() && ei->d_has_neg_pto.get() ){
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      if (fact.getKind() == kind::NOT)
      {
        TNode atom = fact[0];
        Assert(atom.getKind() == kind::SEP_LABEL);
        TNode satom = atom[0];
        if (satom.getKind() == SEP_PTO)
        {
          if( areEqual( atom[1], ei_n ) ){
            addPto( ei, ei_n, atom, false );
          }
        }
      }
    }
    //we have now processed all pending negated pto
    ei->d_has_neg_pto.set( false );
  }
}

void TheorySep::addPto( HeapAssertInfo * ei, Node ei_n, Node p, bool polarity ) {
  Trace("sep-pto") << "Add pto " << p << ", pol = " << polarity << " to eqc " << ei_n << std::endl;
  if( !ei->d_pto.get().isNull() ){
    if( polarity ){
      Trace("sep-pto-debug") << "...eqc " << ei_n << " already has pto " << ei->d_pto.get() << ", merge." << std::endl;
      mergePto( ei->d_pto.get(), p );
    }else{
      Node pb = ei->d_pto.get();
      Trace("sep-pto") << "Process positive/negated pto " << " " << pb << " " << p << std::endl;
      Assert(pb.getKind() == kind::SEP_LABEL
             && pb[0].getKind() == kind::SEP_PTO);
      Assert(p.getKind() == kind::SEP_LABEL && p[0].getKind() == kind::SEP_PTO);
      Assert(areEqual(pb[1], p[1]));
      std::vector< Node > exp;
      if( pb[1]!=p[1] ){
        //if( pb[1].getKind()==kind::SINGLETON && p[1].getKind()==kind::SINGLETON ){
        //  exp.push_back( pb[1][0].eqNode( p[1][0] ) );
        //}else{
        exp.push_back( pb[1].eqNode( p[1] ) );
        //}
      }
      exp.push_back( pb );
      exp.push_back( p.negate() );
      std::vector< Node > conc;
      if( pb[0][1]!=p[0][1] ){
        conc.push_back( pb[0][1].eqNode( p[0][1] ).negate() );
      }
      //if( pb[1]!=p[1] ){
      //  conc.push_back( pb[1].eqNode( p[1] ).negate() );
      //}
      Node n_conc = conc.empty() ? d_false : ( conc.size()==1 ? conc[0] : NodeManager::currentNM()->mkNode( kind::OR, conc ) );
      Trace("sep-pto")  << "Conclusion is " << n_conc << std::endl;
      // propagation for (pto x y) ^ ~(pto z w) ^ x = z => y != w
      sendLemma( exp, n_conc, InferenceId::SEP_PTO_NEG_PROP);
    }
  }else{
    if( polarity ){
      ei->d_pto.set( p );
      validatePto( ei, ei_n );
    }else{
      ei->d_has_neg_pto.set( true );
    }
  }
}

void TheorySep::mergePto( Node p1, Node p2 ) {
  Trace("sep-lemma-debug") << "Merge pto " << p1 << " " << p2 << std::endl;
  Assert(p1.getKind() == kind::SEP_LABEL && p1[0].getKind() == kind::SEP_PTO);
  Assert(p2.getKind() == kind::SEP_LABEL && p2[0].getKind() == kind::SEP_PTO);
  if( !areEqual( p1[0][1], p2[0][1] ) ){
    std::vector< Node > exp;
    if( p1[1]!=p2[1] ){
      Assert(areEqual(p1[1], p2[1]));
      exp.push_back( p1[1].eqNode( p2[1] ) );
    }
    exp.push_back( p1 );
    exp.push_back( p2 );
    //enforces injectiveness of pto : (pto x y) ^ (pto y w) ^ x = y => y = w
    sendLemma( exp, p1[0][1].eqNode( p2[0][1] ), InferenceId::SEP_PTO_PROP);
  }
}

void TheorySep::sendLemma( std::vector< Node >& ant, Node conc, InferenceId id, bool infer ) {
  Trace("sep-lemma-debug") << "Do rewrite on inference : " << conc << std::endl;
  conc = Rewriter::rewrite( conc );
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
        d_im.conflictExp(id, ant, nullptr);
      }else{
        Trace("sep-lemma") << "Sep::Lemma: " << conc << " from " << ant
                           << " by " << id << std::endl;
        TrustNode trn = d_im.mkLemmaExp(conc, ant, {});
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

void TheorySep::debugPrintHeap( HeapInfo& heap, const char * c ) {
  Trace(c) << "[" << std::endl;
  Trace(c) << "  ";
  for( unsigned j=0; j<heap.d_heap_locs.size(); j++ ){
    Trace(c) << heap.d_heap_locs[j] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "]" << std::endl;
}

Node TheorySep::HeapInfo::getValue( TypeNode tn ) {
  Assert(d_heap_locs.size() == d_heap_locs_model.size());
  if( d_heap_locs.empty() ){
    return NodeManager::currentNM()->mkConst(EmptySet(tn));
  }
  Node curr = d_heap_locs[0];
  for (unsigned j = 1; j < d_heap_locs.size(); j++)
  {
    curr = NodeManager::currentNM()->mkNode(kind::UNION, d_heap_locs[j], curr);
  }
  return curr;
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5
