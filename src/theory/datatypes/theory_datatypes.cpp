/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of datatypes.
 */
#include "theory/datatypes/theory_datatypes.h"

#include <map>
#include <sstream>

#include "base/check.h"
#include "expr/codatatype_bound_variable.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/kind.h"
#include "expr/skolem_manager.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "proof/proof_node_manager.h"
#include "smt/logic_exception.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes_type_rules.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/logic_info.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"
#include "theory/type_enumerator.h"
#include "theory/valuation.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

TheoryDatatypes::TheoryDatatypes(Env& env,
                                 OutputChannel& out,
                                 Valuation valuation)
    : Theory(THEORY_DATATYPES, env, out, valuation),
      d_term_sk(userContext()),
      d_labels(context()),
      d_selector_apps(context()),
      d_initialLemmaCache(userContext()),
      d_functionTerms(context()),
      d_singleton_eq(userContext()),
      d_sygusExtension(nullptr),
      d_rewriter(env.getEvaluator(), env.getOptions()),
      d_state(env, valuation),
      d_im(env, *this, d_state),
      d_notify(d_im, *this),
      d_checker(env.getOptions().datatypes.dtSharedSelectors),
      d_cpacb(*this)
{

  d_true = NodeManager::currentNM()->mkConst( true );
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));

  // indicate we are using the default theory state object
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryDatatypes::~TheoryDatatypes() {
  for(std::map< Node, EqcInfo* >::iterator i = d_eqc_info.begin(), iend = d_eqc_info.end();
      i != iend; ++i){
    EqcInfo* current = (*i).second;
    Assert(current != NULL);
    delete current;
  }
}

TheoryRewriter* TheoryDatatypes::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryDatatypes::getProofChecker() { return &d_checker; }

bool TheoryDatatypes::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::datatypes::ee";
  // need notifications on new constructors, merging datatype eqcs
  esi.d_notifyNewClass = true;
  esi.d_notifyMerge = true;
  return true;
}

void TheoryDatatypes::finishInit()
{
  Assert(d_equalityEngine != nullptr);
  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine->addFunctionKind(kind::APPLY_SELECTOR);
  d_equalityEngine->addFunctionKind(kind::APPLY_TESTER);
  // We could but don't do congruence for DT_SIZE and DT_HEIGHT_BOUND here.
  // It also could make sense in practice to do congruence for APPLY_UF, but
  // this is not done.
  // Enable the sygus extension if we will introduce sygus datatypes. This
  // is the case for sygus problems and when using sygus-inst.
  if (getQuantifiersEngine()
      && (options().quantifiers.sygus || options().quantifiers.sygusInst))
  {
    quantifiers::TermDbSygus* tds =
        getQuantifiersEngine()->getTermDatabaseSygus();
    d_sygusExtension.reset(new SygusExtension(d_env, d_state, d_im, tds));
    // do congruence on evaluation functions
    d_equalityEngine->addFunctionKind(kind::DT_SYGUS_EVAL);
  }
  // testers are not relevant for model building
  d_valuation.setIrrelevantKind(APPLY_TESTER);
  d_valuation.setIrrelevantKind(DT_SYGUS_BOUND);
  // selectors don't always evaluate
  d_valuation.setUnevaluatedKind(APPLY_SELECTOR);
}

TheoryDatatypes::EqcInfo* TheoryDatatypes::getOrMakeEqcInfo( TNode n, bool doMake ){
  if( !hasEqcInfo( n ) ){
    if( doMake ){
      //add to labels
      d_labels[ n ] = 0;

      std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
      EqcInfo* ei;
      if( eqc_i != d_eqc_info.end() ){
        ei = eqc_i->second;
      }else{
        ei = new EqcInfo(context());
        d_eqc_info[n] = ei;
      }
      if( n.getKind()==APPLY_CONSTRUCTOR ){
        ei->d_constructor = n;
      }

      //add to selectors
      d_selector_apps[n] = 0;

      return ei;
    }else{
      return NULL;
    }
  }else{
    std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
    return (*eqc_i).second;
  }
}

TNode TheoryDatatypes::getEqcConstructor( TNode r ) {
  if( r.getKind()==APPLY_CONSTRUCTOR ){
    return r;
  }else{
    EqcInfo * ei = getOrMakeEqcInfo( r, false );
    if( ei && !ei->d_constructor.get().isNull() ){
      return ei->d_constructor.get();
    }else{
      return r;
    }
  }
}

bool TheoryDatatypes::preCheck(Effort level)
{
  Trace("datatypes-check") << "TheoryDatatypes::preCheck: " << level
                           << std::endl;
  d_im.process();
  d_im.reset();
  return false;
}

void TheoryDatatypes::postCheck(Effort level)
{
  Trace("datatypes-check") << "TheoryDatatypes::postCheck: " << level
                           << std::endl;
  // Apply any last pending inferences, which may occur if the last processed
  // fact was an internal one and triggered further internal inferences.
  d_im.process();
  if (level == EFFORT_LAST_CALL)
  {
    Assert(d_sygusExtension != nullptr);
    d_sygusExtension->check();
  }
  else if (level == EFFORT_FULL && !d_state.isInConflict()
           && !d_im.hasSentLemma() && !d_valuation.needCheck())
  {
    //check for cycles
    Assert(!d_im.hasPendingFact());
    do {
      d_im.reset();
      Trace("datatypes-proc") << "Check cycles..." << std::endl;
      checkCycles();
      Trace("datatypes-proc") << "...finish check cycles" << std::endl;
      d_im.process();
      if (d_state.isInConflict() || d_im.hasSentLemma())
      {
        return;
      }
    } while (d_im.hasSentFact());

    //check for splits
    Trace("datatypes-debug") << "Check for splits " << endl;
    do {
      d_im.reset();
      // check for splits
      checkSplit();
      if (d_im.hasSentLemma())
      {
        // clear pending facts: we added a lemma, so internal inferences are
        // no longer necessary
        d_im.clearPendingFacts();
      }
      else
      {
        // we did not add a lemma, process internal inferences. This loop
        // will repeat.
        Trace("datatypes-debug") << "Flush pending facts..." << std::endl;
        d_im.process();
      }
    } while (!d_state.isInConflict() && !d_im.hasSentLemma()
             && d_im.hasSentFact());
    Trace("datatypes-debug")
        << "Finished, conflict=" << d_state.isInConflict()
        << ", lemmas=" << d_im.hasSentLemma() << std::endl;
    if (!d_state.isInConflict())
    {
      Trace("dt-model-debug") << std::endl;
      printModelDebug("dt-model-debug");
    }
  }

  Trace("datatypes-check") << "Finished check effort " << level << std::endl;
  Trace("datatypes") << "TheoryDatatypes::check(): done" << std::endl;
}

bool TheoryDatatypes::needsCheckLastEffort() {
  return d_sygusExtension != nullptr;
}

void TheoryDatatypes::notifyFact(TNode atom,
                                 bool polarity,
                                 TNode fact,
                                 bool isInternal)
{
  Trace("datatypes-debug") << "TheoryDatatypes::assertFact : " << fact
                           << ", isInternal = " << isInternal << std::endl;
  // could be sygus-specific
  if (d_sygusExtension)
  {
    d_sygusExtension->assertFact(atom, polarity);
  }
  //add to tester if applicable
  Node t_arg;
  int tindex = utils::isTester(atom, t_arg);
  if (tindex >= 0)
  {
    Trace("dt-tester") << "Assert tester : " << atom << " for " << t_arg << std::endl;
    Node rep = getRepresentative( t_arg );
    EqcInfo* eqc = getOrMakeEqcInfo( rep, true );
    Node tst =
        isInternal ? (polarity ? Node(atom) : atom.notNode()) : Node(fact);
    addTester(tindex, tst, eqc, rep, t_arg);
    Trace("dt-tester") << "Done assert tester." << std::endl;
    Trace("dt-tester") << "Done pending merges." << std::endl;
    if (!d_state.isInConflict() && polarity)
    {
      if (d_sygusExtension)
      {
        Trace("dt-tester") << "Assert tester to sygus : " << atom << std::endl;
        d_sygusExtension->assertTester(tindex, t_arg, atom);
        Trace("dt-tester") << "Done assert tester to sygus." << std::endl;
      }
    }
  }else{
    Trace("dt-tester-debug") << "Assert (non-tester) : " << atom << std::endl;
  }
  Trace("datatypes-debug") << "TheoryDatatypes::assertFact : finished " << fact << std::endl;
  // now, flush pending facts if this wasn't an internal call
  if (!isInternal)
  {
    d_im.process();
  }
}

void TheoryDatatypes::preRegisterTerm(TNode n)
{
  Trace("datatypes-prereg")
      << "TheoryDatatypes::preRegisterTerm() " << n << endl;
  // must ensure the type is well founded and has no nested recursion if
  // the option dtNestedRec is not set to true.
  TypeNode tn = n.getType();
  if (tn.isDatatype())
  {
    const DType& dt = tn.getDType();
    Trace("dt-expand") << "Check properties of " << dt.getName() << std::endl;
    if (!dt.isWellFounded())
    {
      std::stringstream ss;
      ss << "Cannot handle non-well-founded datatype " << dt.getName();
      throw LogicException(ss.str());
    }
    Trace("dt-expand") << "...well-founded ok" << std::endl;
    if (!options().datatypes.dtNestedRec)
    {
      if (dt.hasNestedRecursion())
      {
        std::stringstream ss;
        ss << "Cannot handle nested-recursive datatype " << dt.getName();
        throw LogicException(ss.str());
      }
      Trace("dt-expand") << "...nested recursion ok" << std::endl;
    }
  }
  switch (n.getKind()) {
  case kind::EQUAL:
  case kind::APPLY_TESTER:
    // add predicate trigger for testers and equalities
    // Get triggered for both equal and dis-equal
    d_state.addEqualityEngineTriggerPredicate(n);
    break;
  default:
    // do initial lemmas (e.g. for dt.size)
    registerInitialLemmas(n);
    // Function applications/predicates
    d_equalityEngine->addTerm(n);
    if (d_sygusExtension)
    {
      d_sygusExtension->preRegisterTerm(n);
    }
    break;
  }
  d_im.process();
}

TrustNode TheoryDatatypes::ppRewrite(TNode in, std::vector<SkolemLemma>& lems)
{
  Trace("datatypes") << "TheoryDatatypes::ppRewrite(" << in << ")" << endl;
  // Eliminate DT_SIZE, which is only used for enforcing fairness in sygus.
  // We only assume that DT_SIZE terms are greater than or equal to zero.
  // Note that this ensures that spurious check-model failures are not
  // generated.
  if (in.getKind() == DT_SIZE)
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node k = sm->mkPurifySkolem(in);
    Node lem = nm->mkNode(LEQ, d_zero, k);
    Trace("datatypes-infer")
        << "DtInfer : size geq zero : " << lem << std::endl;
    TrustNode tlem = TrustNode::mkTrustLemma(lem);
    lems.emplace_back(tlem, k);
    return TrustNode::mkTrustRewrite(in, k);
  }
  // first, see if we need to expand definitions
  TrustNode texp = d_rewriter.expandDefinition(in);
  if (!texp.isNull())
  {
    return texp;
  }
  // nothing to do
  return TrustNode::null();
}

TrustNode TheoryDatatypes::ppStaticRewrite(TNode in)
{
  Trace("datatypes") << "TheoryDatatypes::ppStaticRewrite(" << in << ")"
                     << endl;
  if( in.getKind()==EQUAL ){
    Node nn;
    std::vector< Node > rew;
    if (utils::checkClash(in[0], in[1], rew))
    {
      nn = NodeManager::currentNM()->mkConst(false);
    }
    else
    {
      nn = NodeManager::currentNM()->mkAnd(rew);
    }
    if (in != nn)
    {
      return TrustNode::mkTrustRewrite(in, nn, nullptr);
    }
  }
  return TrustNode::null();
}

TrustNode TheoryDatatypes::explain(TNode literal)
{
  return d_im.explainLit(literal);
}

/** called when a new equivalance class is created */
void TheoryDatatypes::eqNotifyNewClass(TNode n)
{
  Kind nk = n.getKind();
  if (nk == APPLY_CONSTRUCTOR)
  {
    Trace("datatypes") << "  Found constructor " << n << endl;
    getOrMakeEqcInfo(n, true);
    if (n.getNumChildren() > 0)
    {
      d_functionTerms.push_back(n);
    }
  }
  if (nk == APPLY_SELECTOR || nk == DT_HEIGHT_BOUND)
  {
    d_functionTerms.push_back(n);
    // we must also record which selectors exist
    Trace("dt-collapse-sel") << "  Found selector " << n << endl;
    Node rep = getRepresentative(n[0]);
    // record it in the selectors
    EqcInfo* eqc = getOrMakeEqcInfo(rep, true);
    // add it to the eqc info
    addSelector(n, eqc, rep);
  }
}

/** called when two equivalance classes have merged */
void TheoryDatatypes::eqNotifyMerge(TNode t1, TNode t2)
{
  if( t1.getType().isDatatype() ){
    Trace("datatypes-merge")
        << "NotifyMerge : " << t1 << " " << t2 << std::endl;
    merge(t1, t2);
  }
}

void TheoryDatatypes::merge( Node t1, Node t2 ){
  if (d_state.isInConflict())
  {
    return;
  }
  Trace("datatypes-merge") << "Merge " << t1 << " " << t2 << std::endl;
  Assert(d_equalityEngine->areEqual(t1, t2));
  EqcInfo* eqc2 = getOrMakeEqcInfo(t2);
  if (eqc2 == nullptr)
  {
    return;
  }
  bool checkInst = false;
  EqcInfo* eqc1 = getOrMakeEqcInfo(t1);
  if (eqc1)
  {
    Trace("datatypes-debug")
        << "  merge eqc info " << eqc2 << " into " << eqc1 << std::endl;
    // check for clash
    TNode cons1 = eqc1->d_constructor.get();
    TNode cons2 = eqc2->d_constructor.get();
    // if both have constructor, then either clash or unification
    if (!cons1.isNull() && !cons2.isNull())
    {
      Trace("datatypes-debug")
          << "  constructors : " << cons1 << " " << cons2 << std::endl;
      Node unifEq = cons1.eqNode(cons2);
      std::vector<Node> rew;
      if (utils::checkClash(cons1, cons2, rew))
      {
        std::vector<Node> conf;
        conf.push_back(unifEq);
        Trace("dt-conflict")
            << "CONFLICT: Clash conflict : " << conf << std::endl;
        d_im.sendDtConflict(conf, InferenceId::DATATYPES_CLASH_CONFLICT);
        return;
      }
      else
      {
        Assert(d_equalityEngine->areEqual(cons1, cons2));
        // do unification
        for (size_t i = 0, nchild = cons1.getNumChildren(); i < nchild; i++)
        {
          if (!d_equalityEngine->areEqual(cons1[i], cons2[i]))
          {
            Node eq = cons1[i].eqNode(cons2[i]);
            d_im.addPendingInference(eq, InferenceId::DATATYPES_UNIF, unifEq);
            Trace("datatypes-infer") << "DtInfer : cons-inj : " << eq << " by "
                                     << unifEq << std::endl;
          }
        }
      }
    }
    Trace("datatypes-debug") << "  instantiated : " << eqc1->d_inst << " "
                             << eqc2->d_inst << std::endl;
    eqc1->d_inst = eqc1->d_inst || eqc2->d_inst;
    if (!cons2.isNull())
    {
      if (cons1.isNull())
      {
        Trace("datatypes-debug")
            << "  must check if it is okay to set the constructor."
            << std::endl;
        checkInst = true;
        addConstructor(eqc2->d_constructor.get(), eqc1, t1);
        if (d_state.isInConflict())
        {
          return;
        }
      }
    }
  }
  else
  {
    Trace("datatypes-debug")
        << "  no eqc info for " << t1 << ", must create" << std::endl;
    // just copy the equivalence class information
    eqc1 = getOrMakeEqcInfo(t1, true);
    eqc1->d_inst.set(eqc2->d_inst);
    eqc1->d_constructor.set(eqc2->d_constructor);
    eqc1->d_selectors.set(eqc2->d_selectors);
  }

  // merge labels
  NodeUIntMap::iterator lbl_i = d_labels.find(t2);
  if (lbl_i != d_labels.end())
  {
    Trace("datatypes-debug")
        << "  merge labels from " << eqc2 << " " << t2 << std::endl;
    size_t n_label = (*lbl_i).second;
    for (size_t i = 0; i < n_label; i++)
    {
      Assert(i < d_labels_data[t2].size());
      Node t = d_labels_data[t2][i];
      Node t_arg = d_labels_args[t2][i];
      unsigned tindex = d_labels_tindex[t2][i];
      addTester(tindex, t, eqc1, t1, t_arg);
      if (d_state.isInConflict())
      {
        Trace("datatypes-debug") << "  conflict!" << std::endl;
        return;
      }
    }
  }
  // merge selectors
  if (!eqc1->d_selectors && eqc2->d_selectors)
  {
    eqc1->d_selectors = true;
    checkInst = true;
  }
  NodeUIntMap::iterator sel_i = d_selector_apps.find(t2);
  if (sel_i != d_selector_apps.end())
  {
    Trace("datatypes-debug")
        << "  merge selectors from " << eqc2 << " " << t2 << std::endl;
    size_t n_sel = (*sel_i).second;
    for (size_t j = 0; j < n_sel; j++)
    {
      addSelector(d_selector_apps_data[t2][j],
                  eqc1,
                  t1,
                  eqc2->d_constructor.get().isNull());
    }
  }
  if (checkInst)
  {
    Trace("datatypes-debug") << "  checking instantiate" << std::endl;
    instantiate(eqc1, t1);
  }
  Trace("datatypes-debug") << "Finished Merge " << t1 << " " << t2 << std::endl;
}

TheoryDatatypes::EqcInfo::EqcInfo(context::Context* c)
    : d_inst(c, false), d_constructor(c, Node::null()), d_selectors(c, false)
{}

bool TheoryDatatypes::hasLabel( EqcInfo* eqc, Node n ){
  return ( eqc && !eqc->d_constructor.get().isNull() ) || !getLabel( n ).isNull();
}

Node TheoryDatatypes::getLabel( Node n ) {
  NodeUIntMap::iterator lbl_i = d_labels.find(n);
  if( lbl_i != d_labels.end() ){
    size_t n_lbl = (*lbl_i).second;
    if( n_lbl>0 && d_labels_data[n][ n_lbl-1 ].getKind()!=kind::NOT ){
      return d_labels_data[n][ n_lbl-1 ];
    }
  }
  return Node::null();
}

int TheoryDatatypes::getLabelIndex( EqcInfo* eqc, Node n ){
  if( eqc && !eqc->d_constructor.get().isNull() ){
    return utils::indexOf(eqc->d_constructor.get().getOperator());
  }else{
    Node lbl = getLabel( n );
    if( lbl.isNull() ){
      return -1;
    }else{
      int tindex = utils::isTester(lbl);
      Trace("datatypes-debug") << "Label of " << n << " is " << lbl
                               << " with tindex " << tindex << std::endl;
      Assert(tindex != -1);
      return tindex;
    }
  }
}

bool TheoryDatatypes::hasTester( Node n ) {
  NodeUIntMap::iterator lbl_i = d_labels.find(n);
  if( lbl_i != d_labels.end() ){
    return (*lbl_i).second>0;
  }else{
    return false;
  }
}

void TheoryDatatypes::getPossibleCons( EqcInfo* eqc, Node n, std::vector< bool >& pcons ){
  TypeNode tn = n.getType();
  const DType& dt = tn.getDType();
  int lindex = getLabelIndex( eqc, n );
  pcons.resize( dt.getNumConstructors(), lindex==-1 );
  if( lindex!=-1 ){
    pcons[ lindex ] = true;
  }else{
    NodeUIntMap::iterator lbl_i = d_labels.find(n);
    if( lbl_i != d_labels.end() ){
      size_t n_lbl = (*lbl_i).second;
      for (size_t i = 0; i < n_lbl; i++)
      {
        Assert(d_labels_data[n][i].getKind() == NOT);
        unsigned tindex = d_labels_tindex[n][i];
        pcons[ tindex ] = false;
      }
    }
  }
}

Node TheoryDatatypes::getTermSkolemFor( Node n ) {
  if( n.getKind()==APPLY_CONSTRUCTOR ){
    NodeMap::const_iterator it = d_term_sk.find( n );
    if( it==d_term_sk.end() ){
      NodeManager* nm = NodeManager::currentNM();
      SkolemManager* sm = nm->getSkolemManager();
      //add purification unit lemma ( k = n )
      Node k = sm->mkPurifySkolem(n);
      d_term_sk[n] = k;
      Node eq = k.eqNode( n );
      Trace("datatypes-infer") << "DtInfer : ref : " << eq << std::endl;
      d_im.addPendingInference(eq, InferenceId::DATATYPES_PURIFY, d_true, true);
      return k;
    }else{
      return (*it).second;
    }
  }else{
    return n;
  }
}

void TheoryDatatypes::addTester(
    unsigned ttindex, Node t, EqcInfo* eqc, Node n, Node t_arg)
{
  Trace("datatypes-debug") << "Add tester : " << t << " to eqc(" << n << ")" << std::endl;
  Trace("datatypes-labels") << "Add tester " << t << " " << n << " " << eqc << std::endl;
  bool tpolarity = t.getKind()!=NOT;
  Assert((tpolarity ? t : t[0]).getKind() == APPLY_TESTER);
  Node j, jt;
  bool makeConflict = false;
  int prevTIndex = getLabelIndex(eqc, n);
  if (prevTIndex >= 0)
  {
    unsigned ptu = static_cast<unsigned>(prevTIndex);
    //if we already know the constructor type, check whether it is in conflict or redundant
    if ((ptu == ttindex) != tpolarity)
    {
      if( !eqc->d_constructor.get().isNull() ){
        //conflict because equivalence class contains a constructor
        std::vector<Node> conf;
        conf.push_back(t);
        conf.push_back(t_arg.eqNode(eqc->d_constructor.get()));
        Trace("dt-conflict")
            << "CONFLICT: Tester eq conflict " << conf << std::endl;
        d_im.sendDtConflict(conf, InferenceId::DATATYPES_TESTER_CONFLICT);
        return;
      }else{
        makeConflict = true;
        //conflict because the existing label is contradictory
        j = getLabel( n );
        jt = j;
      }
    }else{
      return;
    }
  }else{
    //otherwise, scan list of labels
    NodeUIntMap::iterator lbl_i = d_labels.find(n);
    Assert(lbl_i != d_labels.end());
    size_t n_lbl = (*lbl_i).second;
    std::map< int, bool > neg_testers;
    for (size_t i = 0; i < n_lbl; i++)
    {
      Assert(d_labels_data[n][i].getKind() == NOT);
      unsigned jtindex = d_labels_tindex[n][i];
      if( jtindex==ttindex ){
        if( tpolarity ){  //we are in conflict
          j = d_labels_data[n][i];
          jt = j[0];
          makeConflict = true;
          break;
        }else{            //it is redundant
          return;
        }
      }else{
        neg_testers[jtindex] = true;
      }
    }
    if( !makeConflict ){
      Trace("datatypes-labels") << "Add to labels " << t << std::endl;
      d_labels[n] = n_lbl + 1;
      if (n_lbl < d_labels_data[n].size())
      {
        // reuse spot in the vector
        d_labels_data[n][n_lbl] = t;
        d_labels_args[n][n_lbl] = t_arg;
        d_labels_tindex[n][n_lbl] = ttindex;
      }else{
        d_labels_data[n].push_back(t);
        d_labels_args[n].push_back(t_arg);
        d_labels_tindex[n].push_back(ttindex);
      }
      n_lbl++;

      const DType& dt = t_arg.getType().getDType();
      Trace("datatypes-labels") << "Labels at " << n_lbl << " / " << dt.getNumConstructors() << std::endl;
      if( tpolarity ){
        instantiate(eqc, n);
        // We could propagate is-C1(x) => not is-C2(x) here for all other
        // constructors, but empirically this hurts performance.
      }else{
        //check if we have reached the maximum number of testers
        // in this case, add the positive tester
        if (n_lbl == dt.getNumConstructors() - 1)
        {
          std::vector< bool > pcons;
          getPossibleCons( eqc, n, pcons );
          int testerIndex = -1;
          for( unsigned i=0; i<pcons.size(); i++ ) {
            if( pcons[i] ){
              testerIndex = i;
              break;
            }
          }
          Assert(testerIndex != -1);
          //we must explain why each term in the set of testers for this equivalence class is equal
          std::vector< Node > eq_terms;
          NodeBuilder nb(kind::AND);
          for (unsigned i = 0; i < n_lbl; i++)
          {
            Node ti = d_labels_data[n][i];
            nb << ti;
            Assert(ti.getKind() == NOT);
            Node t_arg2 = d_labels_args[n][i];
            if( std::find( eq_terms.begin(), eq_terms.end(), t_arg2 )==eq_terms.end() ){
              eq_terms.push_back( t_arg2 );
              if( t_arg2!=t_arg ){
                nb << t_arg2.eqNode( t_arg );
              }
            }
          }
          Node t_concl = testerIndex == -1
                             ? NodeManager::currentNM()->mkConst(false)
                             : utils::mkTester(t_arg, testerIndex, dt);
          Node t_concl_exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
          d_im.addPendingInference(
              t_concl, InferenceId::DATATYPES_LABEL_EXH, t_concl_exp);
          Trace("datatypes-infer") << "DtInfer : label : " << t_concl << " by " << t_concl_exp << std::endl;
          return;
        }
      }
    }
  }
  if( makeConflict ){
    Trace("datatypes-labels") << "Explain " << j << " " << t << std::endl;
    std::vector<Node> conf;
    conf.push_back(j);
    conf.push_back(t);
    if (jt[0] != t_arg)
    {
      conf.push_back(jt[0].eqNode(t_arg));
    }
    Trace("dt-conflict") << "CONFLICT: Tester conflict : " << conf << std::endl;
    d_im.sendDtConflict(conf, InferenceId::DATATYPES_TESTER_MERGE_CONFLICT);
  }
}

void TheoryDatatypes::addSelector( Node s, EqcInfo* eqc, Node n, bool assertFacts ) {
  Trace("dt-collapse-sel") << "Add selector : " << s << " to eqc(" << n << ")" << std::endl;
  //check to see if it is redundant
  NodeUIntMap::iterator sel_i = d_selector_apps.find(n);
  Assert(sel_i != d_selector_apps.end());
  if( sel_i != d_selector_apps.end() ){
    size_t n_sel = (*sel_i).second;
    for (size_t j = 0; j < n_sel; j++)
    {
      Node ss = d_selector_apps_data[n][j];
      if( s.getOperator()==ss.getOperator() && ( s.getKind()!=DT_HEIGHT_BOUND || s[1]==ss[1] ) ){
        Trace("dt-collapse-sel") << "...redundant." << std::endl;
        return;
      }
    }
    d_selector_apps[n] = n_sel + 1;
    if (n_sel < d_selector_apps_data[n].size())
    {
      d_selector_apps_data[n][n_sel] = s;
    }else{
      d_selector_apps_data[n].push_back( s );
    }

    eqc->d_selectors = true;
  }
  if( assertFacts && !eqc->d_constructor.get().isNull() ){
    //conclude the collapsed merge
    collapseSelector( s, eqc->d_constructor.get() );
  }
}

void TheoryDatatypes::addConstructor( Node c, EqcInfo* eqc, Node n ){
  Trace("datatypes-debug") << "Add constructor : " << c << " to eqc(" << n << ")" << std::endl;
  Assert(eqc->d_constructor.get().isNull());
  //check labels
  NodeUIntMap::iterator lbl_i = d_labels.find(n);
  if( lbl_i != d_labels.end() ){
    size_t constructorIndex = utils::indexOf(c.getOperator());
    size_t n_lbl = (*lbl_i).second;
    for (size_t i = 0; i < n_lbl; i++)
    {
      Node t = d_labels_data[n][i];
      if (d_labels_data[n][i].getKind() == NOT)
      {
        unsigned tindex = d_labels_tindex[n][i];
        if (tindex == constructorIndex)
        {
          std::vector<Node> conf;
          conf.push_back(t);
          conf.push_back(t[0][0].eqNode(c));
          Trace("dt-conflict")
              << "CONFLICT: Tester merge eq conflict : " << conf << std::endl;
          d_im.sendDtConflict(conf, InferenceId::DATATYPES_TESTER_CONFLICT);
          return;
        }
      }
    }
  }
  //check selectors
  NodeUIntMap::iterator sel_i = d_selector_apps.find(n);
  if( sel_i != d_selector_apps.end() ){
    size_t n_sel = (*sel_i).second;
    for (size_t j = 0; j < n_sel; j++)
    {
      Node s = d_selector_apps_data[n][j];
      //collapse the selector
      collapseSelector( s, c );
    }
  }
  eqc->d_constructor.set( c );
}

void TheoryDatatypes::collapseSelector( Node s, Node c ) {
  Assert(c.getKind() == APPLY_CONSTRUCTOR);
  Trace("dt-collapse-sel") << "collapse selector : " << s << " " << c << std::endl;
  Node r;
  bool wrong = false;
  Node eq_exp = s[0].eqNode(c);
  if (s.getKind() == kind::APPLY_SELECTOR)
  {
    Node selector = s.getOperator();
    size_t constructorIndex = utils::indexOf(c.getOperator());
    const DType& dt = utils::datatypeOf(selector);
    const DTypeConstructor& dtc = dt[constructorIndex];
    int selectorIndex = dtc.getSelectorIndexInternal(selector);
    Trace("dt-collapse-sel")
        << "selector index is " << selectorIndex << std::endl;
    wrong = selectorIndex<0;
    r = NodeManager::currentNM()->mkNode(
        kind::APPLY_SELECTOR, s.getOperator(), c);
  }
  if( !r.isNull() ){
    Node rrs;
    if (wrong)
    {
      // If the selector application was wrong, we do nothing. The selector
      // term in this context will be unevaluated, and treated via congruence.
      return;
    }
    else
    {
      rrs = rewrite(r);
    }
    if (s != rrs)
    {
      Node eq = s.eqNode(rrs);
      // Since collapsing selectors may generate new terms, we must send
      // this out as a lemma if it is of an external type, or otherwise we
      // may ask for the equality status of terms that only datatypes knows
      // about, see issue #5344.
      bool forceLemma = !s.getType().isDatatype();
      Trace("datatypes-infer") << "DtInfer : collapse sel";
      Trace("datatypes-infer") << " : " << eq << " by " << eq_exp << std::endl;
      d_im.addPendingInference(
          eq, InferenceId::DATATYPES_COLLAPSE_SEL, eq_exp, forceLemma);
    }
  }
}

EqualityStatus TheoryDatatypes::getEqualityStatus(TNode a, TNode b){
  Assert(d_equalityEngine->hasTerm(a) && d_equalityEngine->hasTerm(b));
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
  return EQUALITY_FALSE_IN_MODEL;
}

void TheoryDatatypes::computeCareGraph(){
  Trace("dt-cg-summary") << "Compute graph for dt..." << d_functionTerms.size() << " " << d_sharedTerms.size() << std::endl;
  Trace("dt-cg") << "Build indices..." << std::endl;
  std::map<TypeNode, std::map<Node, TNodeTrie> > index;
  std::map< Node, unsigned > arity;
  //populate indices
  unsigned functionTerms = d_functionTerms.size();
  for( unsigned i=0; i<functionTerms; i++ ){
    TNode f1 = d_functionTerms[i];
    Assert(d_equalityEngine->hasTerm(f1));
    Trace("dt-cg-debug") << "...build for " << f1 << std::endl;
    // Break into index based on operator.
    // To handle parameteric datatypes, we also indexed based on the overall
    // type if a constructor, or the type of the argument (e.g. if a selector)
    // otherwise
    Node op = f1.getOperator();
    TypeNode tn =
        f1.getKind() == APPLY_CONSTRUCTOR ? f1.getType() : f1[0].getType();
    std::vector< TNode > reps;
    bool has_trigger_arg = false;
    for( unsigned j=0; j<f1.getNumChildren(); j++ ){
      reps.push_back(d_equalityEngine->getRepresentative(f1[j]));
      if (d_equalityEngine->isTriggerTerm(f1[j], THEORY_DATATYPES))
      {
        has_trigger_arg = true;
      }
    }
    Trace("dt-cg-debug") << "...has trigger arg = " << has_trigger_arg
                         << std::endl;
    //only may contribute to care pairs if has at least one trigger argument
    if( has_trigger_arg ){
      index[tn][op].addTerm( f1, reps );
      arity[op] = reps.size();
    }
  }
  //for each index
  for (std::pair<const TypeNode, std::map<Node, TNodeTrie> >& tt : index)
  {
    for (std::pair<const Node, TNodeTrie>& t : tt.second)
    {
      Trace("dt-cg") << "Process index " << tt.first << ", " << t.first << "..."
                     << std::endl;
      nodeTriePathPairProcess(&t.second, arity[t.first], d_cpacb);
      Trace("dt-cg") << "...finish" << std::endl;
    }
  }
  Trace("dt-cg-summary") << "...done" << std::endl;
}

bool TheoryDatatypes::collectModelValues(TheoryModel* m,
                                         const std::set<Node>& termSet)
{
  Trace("dt-cmi") << "Datatypes : Collect model values "
                  << d_equalityEngine->consistent() << std::endl;
  Trace("dt-model") << std::endl;
  printModelDebug( "dt-model" );
  Trace("dt-model") << std::endl;

  //get all constructors
  eq::EqClassesIterator eqccs_i = eq::EqClassesIterator(d_equalityEngine);
  std::vector< Node > nodes;
  std::map< Node, Node > eqc_cons;
  while( !eqccs_i.isFinished() ){
    Node eqc = (*eqccs_i);
    if( eqc.getType().isDatatype() ){
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      if( ei && !ei->d_constructor.get().isNull() ){
        Node c = ei->d_constructor.get();
        eqc_cons[ eqc ] = c;
      }else{
        //if eqc contains a symbol known to datatypes (a selector), then we must assign
        //should assign constructors to EQC if they have a selector or a tester
        bool shouldConsider = ( ei && ei->d_selectors ) || hasTester( eqc );
        if( shouldConsider ){
          nodes.push_back( eqc );
        }
      }
    }
    //}
    ++eqccs_i;
  }

  std::map< TypeNode, int > typ_enum_map;
  std::vector< TypeEnumerator > typ_enum;
  size_t index = 0;
  bool shareSel = options().datatypes.dtSharedSelectors;
  while (index < nodes.size())
  {
    Node eqc = nodes[index];
    Node neqc;
    TypeNode tt = eqc.getType();
    const DType& dt = tt.getDType();
    if (!d_equalityEngine->hasTerm(eqc))
    {
      Assert(false);
    }else{
      Trace("dt-cmi") << "NOTICE : Datatypes: no constructor in equivalence class " << eqc << std::endl;
      Trace("dt-cmi") << "   Type : " << eqc.getType() << std::endl;
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      std::vector< bool > pcons;
      getPossibleCons( ei, eqc, pcons );
      Trace("dt-cmi") << "Possible constructors : ";
      for( unsigned i=0; i<pcons.size(); i++ ){
        Trace("dt-cmi") << pcons[i] << " ";
      }
      Trace("dt-cmi") << std::endl;
      for (size_t r = 0; r < 2; r++)
      {
        if( neqc.isNull() ){
          for (size_t i = 0, psize = pcons.size(); i < psize; i++)
          {
            // must try the infinite ones first
            bool cfinite =
                d_env.isFiniteType(dt[i].getInstantiatedConstructorType(tt));
            if( pcons[i] && (r==1)==cfinite ){
              neqc = utils::getInstCons(eqc, dt, i, shareSel);
              break;
            }
          }
        }
      }
    }
    if( !neqc.isNull() ){
      Trace("dt-cmi") << "Assign : " << neqc << std::endl;
      if (!m->assertEquality(eqc, neqc, true))
      {
        return false;
      }
      eqc_cons[ eqc ] = neqc;
    }
    ++index;
  }

  for( std::map< Node, Node >::iterator it = eqc_cons.begin(); it != eqc_cons.end(); ++it ){
    Node eqc = it->first;
    if( eqc.getType().isCodatatype() ){
      //must proactive expand to avoid looping behavior in model builder
      if( !it->second.isNull() ){
        std::map< Node, int > vmap;
        Node v = getCodatatypesValue( it->first, eqc_cons, vmap, 0 );
        Trace("dt-cmi") << "  EQC(" << it->first << "), constructor is " << it->second << ", value is " << v << ", const = " << v.isConst() << std::endl;
        if (!m->assertEquality(eqc, v, true))
        {
          return false;
        }
        m->assertSkeleton(v);
      }
    }else{
      Trace("dt-cmi") << "Datatypes : assert representative " << it->second << " for " << it->first << std::endl;
      m->assertSkeleton(it->second);
    }
  }
  return true;
}


Node TheoryDatatypes::getCodatatypesValue( Node n, std::map< Node, Node >& eqc_cons, std::map< Node, int >& vmap, int depth ){
  std::map< Node, int >::iterator itv = vmap.find( n );
  NodeManager* nm = NodeManager::currentNM();
  if( itv!=vmap.end() ){
    int debruijn = depth - 1 - itv->second;
    return nm->mkConst(CodatatypeBoundVariable(n.getType(), debruijn));
  }else if( n.getType().isDatatype() ){
    Node nc = eqc_cons[n];
    if( !nc.isNull() ){
      vmap[n] = depth;
      Trace("dt-cmi-cdt-debug") << "    map " << n << " -> " << depth << std::endl;
      Assert(nc.getKind() == APPLY_CONSTRUCTOR);
      std::vector< Node > children;
      children.push_back( nc.getOperator() );
      for( unsigned i=0; i<nc.getNumChildren(); i++ ){
        Node r = getRepresentative( nc[i] );
        Node rv = getCodatatypesValue( r, eqc_cons, vmap, depth+1 );
        children.push_back( rv );
      }
      vmap.erase( n );
      return nm->mkNode(APPLY_CONSTRUCTOR, children);
    }
  }
  return n;
}

Node TheoryDatatypes::getSingletonLemma( TypeNode tn, bool pol ) {
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  int index = pol ? 0 : 1;
  std::map< TypeNode, Node >::iterator it = d_singleton_lemma[index].find( tn );
  if( it==d_singleton_lemma[index].end() ){
    Node a;
    if( pol ){
      Node v1 = nm->mkBoundVar(tn);
      Node v2 = nm->mkBoundVar(tn);
      a = nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, v1, v2), v1.eqNode(v2));
    }else{
      Node v1 = sm->mkDummySkolem("k1", tn);
      Node v2 = sm->mkDummySkolem("k2", tn);
      a = v1.eqNode( v2 ).negate();
      //send out immediately as lemma
      d_im.lemma(a, InferenceId::DATATYPES_REC_SINGLETON_FORCE_DEQ);
      Trace("dt-singleton") << "******** assert " << a << " to avoid singleton cardinality for type " << tn << std::endl;
    }
    d_singleton_lemma[index][tn] = a;
    return a;
  }else{
    return it->second;
  }
}

void TheoryDatatypes::registerInitialLemmas(Node n)
{
  if (d_initialLemmaCache.find(n) != d_initialLemmaCache.end())
  {
    return;
  }
  d_initialLemmaCache[n] = true;

  NodeManager* nm = NodeManager::currentNM();
  Kind nk = n.getKind();
  if (nk == DT_HEIGHT_BOUND && n[1].getConst<Rational>().isZero())
  {
    std::vector<Node> children;
    const DType& dt = n[0].getType().getDType();
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      if (utils::isNullaryConstructor(dt[i]))
      {
        Node test = utils::mkTester(n[0], i, dt);
        children.push_back(test);
      }
    }
    Node lem;
    if (children.empty())
    {
      lem = n.negate();
    }
    else
    {
      lem = n.eqNode(children.size() == 1 ? children[0]
                                          : nm->mkNode(OR, children));
    }
    Trace("datatypes-infer") << "DtInfer : zero height : " << lem << std::endl;
    d_im.addPendingLemma(lem, InferenceId::DATATYPES_HEIGHT_ZERO);
  }
}

Node TheoryDatatypes::getInstantiateCons(Node n, const DType& dt, int index)
{
  if( n.getKind()==APPLY_CONSTRUCTOR && n.getNumChildren()==0 ){
    return n;
  }
  //add constructor to equivalence class
  Node k = getTermSkolemFor( n );
  Node n_ic =
      utils::getInstCons(k, dt, index, options().datatypes.dtSharedSelectors);
  Assert (n_ic == rewrite(n_ic));
  Trace("dt-enum") << "Made instantiate cons " << n_ic << std::endl;
  return n_ic;
}

bool TheoryDatatypes::instantiate(EqcInfo* eqc, Node n)
{
  Trace("datatypes-debug") << "Instantiate: " << n << std::endl;
  //add constructor to equivalence class if not done so already
  int index = getLabelIndex( eqc, n );
  if (index == -1 || eqc->d_inst)
  {
    return false;
  }
  Node exp;
  Node tt;
  if (!eqc->d_constructor.get().isNull())
  {
    exp = d_true;
    tt = eqc->d_constructor;
  }
  else
  {
    exp = getLabel(n);
    tt = exp[0];
  }
  TypeNode ttn = tt.getType();
  const DType& dt = ttn.getDType();
  // instantiate this equivalence class
  eqc->d_inst = true;
  Node tt_cons = getInstantiateCons(tt, dt, index);
  if (tt == tt_cons)
  {
    // not necessary
    return false;
  }
  Node eq = tt.eqNode(tt_cons);
  // Determine if the equality must be sent out as a lemma. Notice that
  // we  keep new equalities from the instantiate rule internal
  // as long as they are for datatype constructors that have no arguments that
  // have finite external type, which corresponds to:
  //   forceLemma = dt[index].hasFiniteExternalArgType(ttn);
  // Such equalities must be sent because they introduce selector terms that
  // may contribute to conflicts due to cardinality (good examples of this are
  // regress0/datatypes/dt-param-card4-bool-sat.smt2 and
  // regress0/datatypes/list-bool.smt2).
  bool forceLemma;
  if (options().datatypes.dtPoliteOptimize)
  {
    forceLemma = dt[index].hasFiniteExternalArgType(ttn);
  }
  else
  {
    forceLemma = dt.involvesExternalType();
  }
  Trace("datatypes-infer-debug") << "DtInstantiate : " << eqc << " " << eq
                                 << " forceLemma = " << forceLemma << std::endl;
  Trace("datatypes-infer") << "DtInfer : instantiate : " << eq << " by " << exp
                           << std::endl;
  d_im.addPendingInference(eq, InferenceId::DATATYPES_INST, exp, forceLemma);
  return true;
}

void TheoryDatatypes::checkCycles() {
  Trace("datatypes-cycle-check") << "Check acyclicity" << std::endl;
  std::vector< Node > cdt_eqc;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( tn.isDatatype() ) {
      if( !tn.isCodatatype() ){
        if (options().datatypes.dtCyclic)
        {
          //do cycle checks
          std::map< TNode, bool > visited;
          std::map< TNode, bool > proc;
          std::vector<Node> expl;
          Trace("datatypes-cycle-check") << "...search for cycle starting at " << eqc << std::endl;
          Node cn = searchForCycle( eqc, eqc, visited, proc, expl );
          Trace("datatypes-cycle-check") << "...finish." << std::endl;
          //if we discovered a different cycle while searching this one
          if( !cn.isNull() && cn!=eqc ){
            visited.clear();
            proc.clear();
            expl.clear();
            Node prev = cn;
            cn = searchForCycle( cn, cn, visited, proc, expl );
            Assert(prev == cn);
          }

          if( !cn.isNull() ) {
            Assert(expl.size() > 0);
            Trace("dt-conflict")
                << "CONFLICT: Cycle conflict : " << expl << std::endl;
            d_im.sendDtConflict(expl, InferenceId::DATATYPES_CYCLE);
            return;
          }
        }
      }else{
        //indexing
        cdt_eqc.push_back( eqc );
      }
    }
    ++eqcs_i;
  }
  Trace("datatypes-cycle-check") << "Check uniqueness" << std::endl;
  //process codatatypes
  if (cdt_eqc.size() > 1 && options().datatypes.cdtBisimilar)
  {
    printModelDebug("dt-cdt-debug");
    Trace("dt-cdt-debug") << "Process " << cdt_eqc.size() << " co-datatypes" << std::endl;
    std::vector< std::vector< Node > > part_out;
    std::vector<Node> exp;
    std::map< Node, Node > cn;
    std::map< Node, std::map< Node, int > > dni;
    for( unsigned i=0; i<cdt_eqc.size(); i++ ){
      cn[cdt_eqc[i]] = cdt_eqc[i];
    }
    separateBisimilar( cdt_eqc, part_out, exp, cn, dni, 0, false );
    Trace("dt-cdt-debug") << "Done separate bisimilar." << std::endl;
    if( !part_out.empty() ){
      Trace("dt-cdt-debug") << "Process partition size " << part_out.size() << std::endl;
      for( unsigned i=0; i<part_out.size(); i++ ){
        std::vector< Node > part;
        part.push_back( part_out[i][0] );
        for( unsigned j=1; j<part_out[i].size(); j++ ){
          Trace("dt-cdt") << "Codatatypes : " << part_out[i][0] << " and " << part_out[i][j] << " must be equal!!" << std::endl;
          part.push_back( part_out[i][j] );
          std::vector< std::vector< Node > > tpart_out;
          exp.clear();
          cn.clear();
          cn[part_out[i][0]] = part_out[i][0];
          cn[part_out[i][j]] = part_out[i][j];
          dni.clear();
          separateBisimilar( part, tpart_out, exp, cn, dni, 0, true );
          Assert(tpart_out.size() == 1 && tpart_out[0].size() == 2);
          part.pop_back();
          //merge based on explanation
          Trace("dt-cdt") << "  exp is : ";
          for( unsigned k=0; k<exp.size(); k++ ){
            Trace("dt-cdt") << exp[k] << " ";
          }
          Trace("dt-cdt") << std::endl;
          Node eq = part_out[i][0].eqNode( part_out[i][j] );
          Node eqExp = NodeManager::currentNM()->mkAnd(exp);
          d_im.addPendingInference(eq, InferenceId::DATATYPES_BISIMILAR, eqExp);
          Trace("datatypes-infer") << "DtInfer : cdt-bisimilar : " << eq << " by " << eqExp << std::endl;
        }
      }
    }
  }
}

//everything is in terms of representatives
void TheoryDatatypes::separateBisimilar(
    std::vector<Node>& part,
    std::vector<std::vector<Node> >& part_out,
    std::vector<Node>& exp,
    std::map<Node, Node>& cn,
    std::map<Node, std::map<Node, int> >& dni,
    int dniLvl,
    bool mkExp)
{
  if( !mkExp ){
    Trace("dt-cdt-debug") << "Separate bisimilar : " << std::endl;
    for( unsigned i=0; i<part.size(); i++ ){
      Trace("dt-cdt-debug") << "   " << part[i] << ", current = " << cn[part[i]] << std::endl;
    }
  }
  Assert(part.size() > 1);
  std::map< Node, std::vector< Node > > new_part;
  std::map< Node, std::vector< Node > > new_part_c;
  std::map< int, std::vector< Node > > new_part_rec;

  std::map< Node, Node > cn_cons;
  for( unsigned j=0; j<part.size(); j++ ){
    Node c = cn[part[j]];
    std::map< Node, int >::iterator it_rec = dni[part[j]].find( c );
    if( it_rec!=dni[part[j]].end() ){
      //looped
      if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is looping at index " << it_rec->second << std::endl; }
      new_part_rec[ it_rec->second ].push_back( part[j] );
    }else{
      if( c.getType().isDatatype() ){
        Node ncons = getEqcConstructor( c );
        if( ncons.getKind()==APPLY_CONSTRUCTOR ) {
          Node cc = ncons.getOperator();
          cn_cons[part[j]] = ncons;
          if (mkExp && c != ncons)
          {
            exp.push_back(c.eqNode(ncons));
          }
          new_part[cc].push_back( part[j] );
          if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is datatype " << ncons << "." << std::endl; }
        }else{
          new_part_c[c].push_back( part[j] );
          if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is unspecified datatype." << std::endl; }
        }
      }else{
        //add equivalences
        if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is term " << c << "." << std::endl; }
        new_part_c[c].push_back( part[j] );
      }
    }
  }
  //direct add for constants
  for( std::map< Node, std::vector< Node > >::iterator it = new_part_c.begin(); it != new_part_c.end(); ++it ){
    if( it->second.size()>1 ){
      std::vector< Node > vec;
      vec.insert( vec.begin(), it->second.begin(), it->second.end() );
      part_out.push_back( vec );
    }
  }
  //direct add for recursive
  for( std::map< int, std::vector< Node > >::iterator it = new_part_rec.begin(); it != new_part_rec.end(); ++it ){
    if( it->second.size()>1 ){
      std::vector< Node > vec;
      vec.insert( vec.begin(), it->second.begin(), it->second.end() );
      part_out.push_back( vec );
    }else{
      //add back : could match a datatype?
    }
  }
  //recurse for the datatypes
  for( std::map< Node, std::vector< Node > >::iterator it = new_part.begin(); it != new_part.end(); ++it ){
    if( it->second.size()>1 ){
      //set dni to check for loops
      std::map< Node, Node > dni_rem;
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node n = it->second[i];
        dni[n][cn[n]] = dniLvl;
        dni_rem[n] = cn[n];
      }

      //we will split based on the arguments of the datatype
      std::vector< std::vector< Node > > split_new_part;
      split_new_part.push_back( it->second );

      unsigned nChildren = cn_cons[it->second[0]].getNumChildren();
      //for each child of constructor
      unsigned cindex = 0;
      while( cindex<nChildren && !split_new_part.empty() ){
        if( !mkExp ){ Trace("dt-cdt-debug") << "Split argument #" << cindex << " of " << it->first << "..." << std::endl; }
        std::vector< std::vector< Node > > next_split_new_part;
        for( unsigned j=0; j<split_new_part.size(); j++ ){
          //set current node
          for( unsigned k=0; k<split_new_part[j].size(); k++ ){
            Node n = split_new_part[j][k];
            Node cnc = cn_cons[n][cindex];
            Node nr = getRepresentative(cnc);
            cn[n] = nr;
            if (mkExp && cnc != nr)
            {
              exp.push_back(nr.eqNode(cnc));
            }
          }
          std::vector< std::vector< Node > > c_part_out;
          separateBisimilar( split_new_part[j], c_part_out, exp, cn, dni, dniLvl+1, mkExp );
          next_split_new_part.insert( next_split_new_part.end(), c_part_out.begin(), c_part_out.end() );
        }
        split_new_part.clear();
        split_new_part.insert( split_new_part.end(), next_split_new_part.begin(), next_split_new_part.end() );
        cindex++;
      }
      part_out.insert( part_out.end(), split_new_part.begin(), split_new_part.end() );

      for( std::map< Node, Node >::iterator it2 = dni_rem.begin(); it2 != dni_rem.end(); ++it2 ){
        dni[it2->first].erase( it2->second );
      }
    }
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
Node TheoryDatatypes::searchForCycle(TNode n,
                                     TNode on,
                                     std::map<TNode, bool>& visited,
                                     std::map<TNode, bool>& proc,
                                     std::vector<Node>& explanation,
                                     bool firstTime)
{
  Trace("datatypes-cycle-check2") << "Search for cycle " << n << " " << on << endl;
  TNode ncons;
  TNode nn;
  if( !firstTime ){
    nn = getRepresentative( n );
    if( nn==on ){
      if (n != nn)
      {
        explanation.push_back(n.eqNode(nn));
      }
      return on;
    }
  }else{
    nn = getRepresentative( n );
  }
  if( proc.find( nn )!=proc.end() ){
    return Node::null();
  }
  Trace("datatypes-cycle-check2") << "...representative : " << nn << " " << ( visited.find( nn ) == visited.end() ) << " " << visited.size() << std::endl;
  if( visited.find( nn ) == visited.end() ) {
    Trace("datatypes-cycle-check2") << "  visit : " << nn << std::endl;
    visited[nn] = true;
    TNode nncons = getEqcConstructor(nn);
    if (nncons.getKind() == APPLY_CONSTRUCTOR)
    {
      for (unsigned i = 0; i < nncons.getNumChildren(); i++)
      {
        TNode cn =
            searchForCycle(nncons[i], on, visited, proc, explanation, false);
        if( cn==on ) {
          //add explanation for why the constructor is connected
          if (n != nncons)
          {
            explanation.push_back(n.eqNode(nncons));
          }
          return on;
        }else if( !cn.isNull() ){
          return cn;
        }
      }
    }
    Trace("datatypes-cycle-check2") << "  unvisit : " << nn << std::endl;
    proc[nn] = true;
    visited.erase( nn );
    return Node::null();
  }else{
    TypeNode tn = nn.getType();
    if( tn.isDatatype() ) {
      if( !tn.isCodatatype() ){
        return nn;
      }
    }
    return Node::null();
  }
}

void TheoryDatatypes::checkSplit()
{
  // get the relevant term set, currently all datatype equivalence classes
  // in the equality engine
  std::set<Node> termSetReps;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    ++eqcs_i;
    if (eqc.getType().isDatatype())
    {
      termSetReps.insert(eqc);
    }
  }
  std::map<TypeNode, Node> rec_singletons;
  for (const Node& n : termSetReps)
  {
    Trace("datatypes-debug") << "Process equivalence class " << n << std::endl;
    EqcInfo* eqc = getOrMakeEqcInfo(n);
    // if there are more than 1 possible constructors for eqc
    if (hasLabel(eqc, n))
    {
      Trace("datatypes-debug")
          << "Has constructor " << eqc->d_constructor.get() << std::endl;
      continue;
    }
    Trace("datatypes-debug") << "No constructor..." << std::endl;
    TypeNode tn = n.getType();
    const DType& dt = tn.getDType();
    Trace("datatypes-debug")
        << "Datatype " << dt.getName() << " is " << dt.getCardinalityClass(tn)
        << " " << dt.isRecursiveSingleton(tn) << std::endl;
    if (dt.isRecursiveSingleton(tn))
    {
      Trace("datatypes-debug") << "Check recursive singleton..." << std::endl;
      bool isQuantifiedLogic = logicInfo().isQuantified();
      // handle recursive singleton case
      std::map<TypeNode, Node>::iterator itrs = rec_singletons.find(tn);
      if (itrs != rec_singletons.end())
      {
        Node eq = n.eqNode(itrs->second);
        if (d_singleton_eq.find(eq) == d_singleton_eq.end())
        {
          d_singleton_eq[eq] = true;
          // get assumptions
          bool success = true;
          std::vector<Node> assumptions;
          // if there is at least one uninterpreted sort occurring within the
          // datatype and the logic is not quantified, add lemmas ensuring
          // cardinality is more than one,
          //  do not infer the equality if at least one sort was processed.
          // otherwise, if the logic is quantified, under the assumption that
          // all uninterpreted sorts have cardinality one,
          //  infer the equality.
          for (size_t i = 0; i < dt.getNumRecursiveSingletonArgTypes(tn); i++)
          {
            TypeNode type = dt.getRecursiveSingletonArgType(tn, i);
            if (isQuantifiedLogic)
            {
              // under the assumption that the cardinality of this type is one
              Node a = getSingletonLemma(type, true);
              assumptions.push_back(a.negate());
            }
            else
            {
              success = false;
              // assert that the cardinality of this type is more than one
              getSingletonLemma(type, false);
            }
          }
          if (success)
          {
            Node assumption = n.eqNode(itrs->second);
            assumptions.push_back(assumption);
            Node lemma =
                assumptions.size() == 1
                    ? assumptions[0]
                    : NodeManager::currentNM()->mkNode(OR, assumptions);
            Trace("dt-singleton") << "*************Singleton equality lemma "
                                  << lemma << std::endl;
            d_im.lemma(lemma, InferenceId::DATATYPES_REC_SINGLETON_EQ);
          }
        }
      }
      else
      {
        rec_singletons[tn] = n;
      }
      // do splitting for quantified logics (incomplete anyways)
      if (!isQuantifiedLogic)
      {
        continue;
      }
    }
    Trace("datatypes-debug") << "Get possible cons..." << std::endl;
    // all other cases
    std::vector<bool> pcons;
    getPossibleCons(eqc, n, pcons);
    // check if we do not need to resolve the constructor type for this
    // equivalence class.
    // this is if there are no selectors for this equivalence class, and its
    // possible values are infinite,
    //  then do not split.
    int consIndex = -1;
    int fconsIndex = -1;
    bool needSplit = true;
    for (size_t j = 0, psize = pcons.size(); j < psize; j++)
    {
      if (!pcons[j])
      {
        continue;
      }
      if (consIndex == -1)
      {
        consIndex = j;
      }
      Trace("datatypes-debug") << j << " compute finite..." << std::endl;
      // Notice that we split here on all datatypes except the
      // truly infinite ones. It is possible to also not split
      // on those that are interpreted-finite when finite model
      // finding is disabled, but as a heuristic we choose to split
      // on those too.
      bool ifin = dt[j].getCardinalityClass(tn) != CardinalityClass::INFINITE;
      Trace("datatypes-debug") << "...returned " << ifin << std::endl;
      if (!ifin)
      {
        if (!eqc || !eqc->d_selectors)
        {
          needSplit = false;
          break;
        }
      }
      else if (fconsIndex == -1)
      {
        fconsIndex = j;
      }
    }
    if (!needSplit)
    {
      Trace("dt-split-debug")
          << "Do not split constructor for " << n << " : " << n.getType() << " "
          << dt.getNumConstructors() << std::endl;
      continue;
    }
    if (dt.getNumConstructors() == 1)
    {
      // this may not be necessary?
      // if only one constructor, then this term must be this constructor
      Node t = utils::mkTester(n, 0, dt);
      d_im.addPendingInference(t, InferenceId::DATATYPES_SPLIT, d_true);
      Trace("datatypes-infer")
          << "DtInfer : 1-cons (full) : " << t << std::endl;
    }
    else
    {
      Assert(consIndex != -1 || dt.isSygus());
      if (options().datatypes.dtBinarySplit && consIndex != -1)
      {
        Node test = utils::mkTester(n, consIndex, dt);
        Trace("dt-split") << "*************Split for possible constructor "
                          << dt[consIndex] << " for " << n << endl;
        test = rewrite(test);
        NodeBuilder nb(kind::OR);
        nb << test << test.notNode();
        Node lemma = nb;
        d_im.lemma(lemma, InferenceId::DATATYPES_BINARY_SPLIT);
        d_im.requirePhase(test, true);
      }
      else
      {
        Trace("dt-split") << "*************Split for constructors on " << n
                          << endl;
        Node lemma = utils::mkSplit(n, dt);
        Trace("dt-split-debug") << "Split lemma is : " << lemma << std::endl;
        d_im.sendDtLemma(
            lemma, InferenceId::DATATYPES_SPLIT, LemmaProperty::SEND_ATOMS);
      }
      if (!options().datatypes.dtBlastSplits)
      {
        return;
      }
    }
  }
}

TNode TheoryDatatypes::getRepresentative( TNode a ){
  if (d_equalityEngine->hasTerm(a))
  {
    return d_equalityEngine->getRepresentative(a);
  }
  return a;
}

void TheoryDatatypes::printModelDebug( const char* c ){
  if(! (TraceIsOn(c))) {
    return;
  }

  Trace( c ) << "Datatypes model : " << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
      if( eqc.getType().isDatatype() ){
        Trace( c ) << "DATATYPE : ";
      }
      Trace( c ) << eqc << " : " << eqc.getType() << " : " << std::endl;
      Trace( c ) << "   { ";
      //add terms to model
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
      while( !eqc_i.isFinished() ){
        if( (*eqc_i)!=eqc ){
          Trace( c ) << (*eqc_i) << " ";
        }
        ++eqc_i;
      }
      Trace( c ) << "}" << std::endl;
      if( eqc.getType().isDatatype() ){
        EqcInfo* ei = getOrMakeEqcInfo( eqc );
        if( ei ){
          Trace( c ) << "   Instantiated : " << ei->d_inst.get() << std::endl;
          Trace( c ) << "   Constructor : ";
          if( !ei->d_constructor.get().isNull() ){
            Trace( c )<< ei->d_constructor.get();
          }
          Trace( c ) << std::endl << "   Labels : ";
          if( hasLabel( ei, eqc ) ){
            Trace( c ) << getLabel( eqc );
          }else{
            NodeUIntMap::iterator lbl_i = d_labels.find(eqc);
            if( lbl_i != d_labels.end() ){
              for (size_t j = 0; j < (*lbl_i).second; j++)
              {
                Trace( c ) << d_labels_data[eqc][j] << " ";
              }
            }
          }
          Trace( c ) << std::endl;
          Trace( c ) << "   Selectors : " << ( ei->d_selectors ? "yes, " : "no " );
          NodeUIntMap::iterator sel_i = d_selector_apps.find(eqc);
          if( sel_i != d_selector_apps.end() ){
            for (size_t j = 0; j < (*sel_i).second; j++)
            {
              Trace( c ) << d_selector_apps_data[eqc][j] << " ";
            }
          }
          Trace( c ) << std::endl;
        }
      }
    //}
    ++eqcs_i;
  }
}

void TheoryDatatypes::computeRelevantTerms(std::set<Node>& termSet)
{
  Trace("dt-cmi") << "Have " << termSet.size() << " relevant terms..."
                  << std::endl;

  // Also must include certain constructor terms recorded for each equivalence
  // class (via EqcInfo). These constructor terms may be introduced local to
  // datatypes, are included in the model (collectModelValues), and thus must
  // be included in addition to what termSet would otherwise contain.
  // We furthermore try to change the recorded constructor to be a relevant one
  // from termSet. This avoids model construction errors where the subfields
  // of equated relevant and irrelevant constructor terms may not agree in the
  // model (see issue #9042). In other words, this method ensures that all
  // datatype equivalence classes either:
  // (1) have no (recorded) constructor,
  // (2) have a single recorded constructor term that is not relevant, which we
  // add to termSet below,
  // (3) have (possibly multiple) relevant constructor terms. We ensure the
  // recorded constructor is one of these.
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  while( !eqcs_i.isFinished() ){
    TNode r = (*eqcs_i);
    ++eqcs_i;
    if (!r.getType().isDatatype())
    {
      continue;
    }
    EqcInfo* ei = getOrMakeEqcInfo(r);
    if (!ei || ei->d_constructor.get().isNull())
    {
      // no constructor
      continue;
    }
    if (termSet.find(ei->d_constructor.get()) != termSet.end())
    {
      // the constructor is already relevant
      continue;
    }
    // scan the equivalence class
    bool foundCons = false;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(r, d_equalityEngine);
    while (!eqc_i.isFinished())
    {
      TNode n = *eqc_i;
      ++eqc_i;
      if (n.getKind() == APPLY_CONSTRUCTOR && termSet.find(n) != termSet.end())
      {
        // change the recorded constructor to be a relevant one
        ei->d_constructor = n;
        foundCons = true;
        break;
      }
    }
    // If there are no constructors that are relevant, we consider the
    // recorded constructor to be relevant.
    if (!foundCons)
    {
      termSet.insert(ei->d_constructor.get());
    }
  }
}

std::pair<bool, Node> TheoryDatatypes::entailmentCheck(TNode lit)
{
  Trace("dt-entail") << "Check entailed : " << lit << std::endl;
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  if( atom.getKind()==APPLY_TESTER ){
    Node n = atom[0];
    if (d_equalityEngine->hasTerm(n))
    {
      Node r = d_equalityEngine->getRepresentative(n);
      EqcInfo * ei = getOrMakeEqcInfo( r, false );
      int l_index = getLabelIndex( ei, r );
      int t_index = static_cast<int>(utils::indexOf(atom.getOperator()));
      Trace("dt-entail") << "  Tester indices are " << t_index << " and " << l_index << std::endl;
      if( l_index!=-1 && (l_index==t_index)==pol ){
        std::vector< TNode > exp_c;
        Node eqToExplain;
        if( ei && !ei->d_constructor.get().isNull() ){
          eqToExplain = n.eqNode(ei->d_constructor.get());
        }else{
          Node lbl = getLabel( n );
          Assert(!lbl.isNull());
          exp_c.push_back( lbl );
          Assert(d_equalityEngine->areEqual(n, lbl[0]));
          eqToExplain = n.eqNode(lbl[0]);
        }
        d_equalityEngine->explainLit(eqToExplain, exp_c);
        Node exp = NodeManager::currentNM()->mkAnd(exp_c);
        Trace("dt-entail") << "  entailed, explanation is " << exp << std::endl;
        return make_pair(true, exp);
      }
    }
  }
  return make_pair(false, Node::null());
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
