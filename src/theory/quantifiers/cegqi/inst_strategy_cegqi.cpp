/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of counterexample-guided quantifier instantiation strategies.
 */
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstRewriterCegqi::InstRewriterCegqi(InstStrategyCegqi* p)
    : InstantiationRewriter(), d_parent(p)
{
}

TrustNode InstRewriterCegqi::rewriteInstantiation(
    Node q, const std::vector<Node>& terms, Node inst, bool doVts)
{
  return d_parent->rewriteInstantiation(q, terms, inst, doVts);
}

InstStrategyCegqi::InstStrategyCegqi(Env& env,
                                     QuantifiersState& qs,
                                     QuantifiersInferenceManager& qim,
                                     QuantifiersRegistry& qr,
                                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_irew(new InstRewriterCegqi(this)),
      d_cbqi_set_quant_inactive(false),
      d_incomplete_check(false),
      d_added_cbqi_lemma(userContext()),
      d_small_const_multiplier(NodeManager::currentNM()->mkConstReal(
          Rational(1) / Rational(1000000))),
      d_small_const(d_small_const_multiplier),
      d_freeDeltaLb(userContext(), false)
{
  d_check_vts_lemma_lc = false;
  if (options().quantifiers.cegqiNestedQE)
  {
    d_nestedQe.reset(new NestedQe(d_env));
  }
}

InstStrategyCegqi::~InstStrategyCegqi() {}

bool InstStrategyCegqi::needsCheck(Theory::Effort e)
{
  return e>=Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstStrategyCegqi::needsModel(Theory::Effort e)
{
  size_t nquant = d_treg.getModel()->getNumAssertedQuantifiers();
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = d_treg.getModel()->getAssertedQuantifier(i);
    if (doCbqi(q))
    {
      return QEFFORT_STANDARD;
    }
  }
  return QEFFORT_NONE;
}

bool InstStrategyCegqi::registerCbqiLemma(Node q)
{
  if( !hasAddedCbqiLemma( q ) ){
    NodeManager* nm = NodeManager::currentNM();
    d_added_cbqi_lemma.insert( q );
    Trace("cegqi-debug") << "Do cbqi for " << q << std::endl;
    //add cbqi lemma
    //get the counterexample literal
    Node ceLit = getCounterexampleLiteral(q);
    Node ceBody = d_qreg.getInstConstantBody(q);
    if( !ceBody.isNull() ){
      //add counterexample lemma
      Node lem = NodeManager::currentNM()->mkNode( OR, ceLit.negate(), ceBody.negate() );
      //require any decision on cel to be phase=true
      d_qim.addPendingPhaseRequirement(ceLit, true);
      Trace("cegqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
      //add counterexample lemma
      lem = rewrite(lem);
      Trace("cegqi-lemma") << "Counterexample lemma : " << lem << std::endl;
      registerCounterexampleLemma( q, lem );
      
      //compute dependencies between quantified formulas
      std::vector<Node> ics;
      TermUtil::computeInstConstContains(q, ics);
      d_parent_quant[q].clear();
      d_children_quant[q].clear();
      std::vector<Node> dep;
      for (const Node& ic : ics)
      {
        Node qi = ic.getAttribute(InstConstantAttribute());
        if (std::find(d_parent_quant[q].begin(), d_parent_quant[q].end(), qi)
            == d_parent_quant[q].end())
        {
          d_parent_quant[q].push_back(qi);
          d_children_quant[qi].push_back(q);
          // may not have added the CEX lemma, but the literal is created by
          // the following call regardless. One rare case where this can happen
          // is if both sygus-inst and CEGQI are being run in parallel, and
          // a parent quantified formula is not handled by CEGQI, but a child
          // is.
          Node qicel = getCounterexampleLiteral(qi);
          dep.push_back(qi);
          dep.push_back(qicel);
        }
      }
      if (!dep.empty())
      {
        // This lemma states that if the child is active, then the parent must
        // be asserted, in particular G => Q where G is the CEX literal for the
        // child and Q is the parent.
        Node dep_lemma = nm->mkNode(IMPLIES, ceLit, nm->mkNode(AND, dep));
        Trace("cegqi-lemma")
            << "Counterexample dependency lemma : " << dep_lemma << std::endl;
        d_qim.lemma(dep_lemma, InferenceId::QUANTIFIERS_CEGQI_CEX_DEP);
      }

      //must register all sub-quantifiers of counterexample lemma, register their lemmas
      std::vector< Node > quants;
      TermUtil::computeQuantContains( lem, quants );
      for( unsigned i=0; i<quants.size(); i++ ){
        if( doCbqi( quants[i] ) ){
          registerCbqiLemma( quants[i] );
        }
      }
    }
    // The decision strategy for this quantified formula ensures that its
    // counterexample literal is decided on first. It is user-context dependent.
    std::map<Node, std::unique_ptr<DecisionStrategy>>::iterator itds =
        d_dstrat.find(q);
    DecisionStrategy* dlds = nullptr;
    if (itds == d_dstrat.end())
    {
      d_dstrat[q].reset(new DecisionStrategySingleton(
          d_env, "CexLiteral", ceLit, d_qstate.getValuation()));
      dlds = d_dstrat[q].get();
    }
    else
    {
      dlds = itds->second.get();
    }
    // it is appended to the list of strategies
    d_qim.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_QUANT_CEGQI_FEASIBLE, dlds);
    return true;
  }else{
    return false;
  }
}

void InstStrategyCegqi::reset_round(Theory::Effort effort)
{
  d_cbqi_set_quant_inactive = false;
  d_incomplete_check = false;
  d_active_quant.clear();
  //check if any cbqi lemma has not been added yet
  FirstOrderModel* fm = d_treg.getModel();
  size_t nquant = fm->getNumAssertedQuantifiers();
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
    if( doCbqi( q ) ){
      if (fm->isQuantifierActive(q))
      {
        d_active_quant[q] = true;
        Trace("cegqi-debug") << "Check quantified formula " << q << "..." << std::endl;
        Node cel = getCounterexampleLiteral(q);
        bool value;
        if (d_qstate.getValuation().hasSatValue(cel, value))
        {
          Trace("cegqi-debug") << "...CE Literal has value " << value << std::endl;
          if( !value ){
            if (d_qstate.getValuation().isDecision(cel))
            {
              Trace("cegqi-warn") << "CBQI WARNING: Bad decision on CE Literal." << std::endl;
            }else{
              Trace("cegqi") << "Inactive : " << q << std::endl;
              fm->setQuantifierActive(q, false);
              d_cbqi_set_quant_inactive = true;
              d_active_quant.erase( q );
            }
          }
        }else{
          Trace("cegqi-debug") << "...CE Literal does not have value " << std::endl;
        }
      }
    }
  }

  //refinement: only consider innermost active quantified formulas
  if (options().quantifiers.cegqiInnermost)
  {
    if( !d_children_quant.empty() && !d_active_quant.empty() ){
      Trace("cegqi-debug") << "Find non-innermost quantifiers..." << std::endl;
      std::vector< Node > ninner;
      for( std::map< Node, bool >::iterator it = d_active_quant.begin(); it != d_active_quant.end(); ++it ){
        std::map< Node, std::vector< Node > >::iterator itc = d_children_quant.find( it->first );
        if( itc!=d_children_quant.end() ){
          for( unsigned j=0; j<itc->second.size(); j++ ){
            if( d_active_quant.find( itc->second[j] )!=d_active_quant.end() ){
              Trace("cegqi-debug") << "Do not consider " << it->first << " since it is not innermost (" << itc->second[j] << std::endl;
              ninner.push_back( it->first );
              break;
            }
          }
        }
      } 
      Trace("cegqi-debug") << "Found " << ninner.size() << " non-innermost." << std::endl;
      for( unsigned i=0; i<ninner.size(); i++ ){
        Assert(d_active_quant.find(ninner[i]) != d_active_quant.end());
        d_active_quant.erase( ninner[i] );
      }
      Assert(!d_active_quant.empty());
      Trace("cegqi-debug") << "...done removing." << std::endl;
    }
  }
  d_check_vts_lemma_lc = false;
}

void InstStrategyCegqi::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    Assert(!d_qstate.isInConflict());
    double clSet = 0;
    if( TraceIsOn("cegqi-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cegqi-engine") << "---Cbqi Engine Round, effort = " << e << "---" << std::endl;
    }
    size_t lastWaiting = d_qim.numPendingLemmas();
    for( int ee=0; ee<=1; ee++ ){
      //for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      //  Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      //  if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
      for( std::map< Node, bool >::iterator it = d_active_quant.begin(); it != d_active_quant.end(); ++it ){
        Node q = it->first;
        Trace("cegqi") << "CBQI : Process quantifier " << q[0] << " at effort " << ee << std::endl;
        if (d_qreg.getQuantAttributes().isQuantElimPartial(q))
        {
          d_cbqi_set_quant_inactive = true;
          d_incomplete_check = true;
        }
        process(q, e, ee);
        if (d_qstate.isInConflict())
        {
          break;
        }
      }
      if (d_qstate.isInConflict() || d_qim.numPendingLemmas() > lastWaiting)
      {
        break;
      }
    }
    if( TraceIsOn("cegqi-engine") ){
      if (d_qim.numPendingLemmas() > lastWaiting)
      {
        Trace("cegqi-engine")
            << "Added lemmas = " << (d_qim.numPendingLemmas() - lastWaiting)
            << std::endl;
      }
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cegqi-engine") << "Finished cbqi engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool InstStrategyCegqi::checkComplete(IncompleteId& incId)
{
  if (d_incomplete_check)
  {
    incId = IncompleteId::QUANTIFIERS_CEGQI;
    return false;
  }
  else
  {
    return true;
  }
}

bool InstStrategyCegqi::checkCompleteFor(Node q)
{
  std::map<Node, CegHandledStatus>::iterator it = d_do_cbqi.find(q);
  if( it!=d_do_cbqi.end() ){
    return it->second != CEG_UNHANDLED;
  }else{
    return false;
  }
}

void InstStrategyCegqi::checkOwnership(Node q)
{
  if (d_qreg.getOwner(q) == nullptr && doCbqi(q))
  {
    if (d_do_cbqi[q] == CEG_HANDLED)
    {
      //take full ownership of the quantified formula
      d_qreg.setOwner(q, this);
    }
  }
}

void InstStrategyCegqi::preRegisterQuantifier(Node q)
{
  if (doCbqi(q))
  {
    if (processNestedQe(q, true))
    {
      // will process using nested quantifier elimination
      return;
    }
    // register the cbqi lemma
    if( registerCbqiLemma( q ) ){
      Trace("cegqi") << "Registered cbqi lemma for quantifier : " << q << std::endl;
    }
  }
}
TrustNode InstStrategyCegqi::rewriteInstantiation(
    Node q, const std::vector<Node>& terms, Node inst, bool doVts)
{
  Node prevInst = inst;
  if (doVts)
  {
    // do virtual term substitution
    inst = rewrite(inst);
    Trace("quant-vts-debug") << "Rewrite vts symbols in " << inst << std::endl;
    VtsTermCache* vtc = d_treg.getVtsTermCache();
    inst = vtc->rewriteVtsSymbols(inst);
    Trace("quant-vts-debug") << "...got " << inst << std::endl;
  }
  if (prevInst != inst)
  {
    // not proof producing yet
    return TrustNode::mkTrustRewrite(prevInst, inst, nullptr);
  }
  return TrustNode::null();
}

InstantiationRewriter* InstStrategyCegqi::getInstRewriter() const
{
  return d_irew.get();
}

void InstStrategyCegqi::registerCounterexampleLemma(Node q, Node lem)
{
  // must register with the instantiator
  // must explicitly remove ITEs so that we record dependencies
  std::vector<Node> ce_vars;
  for (size_t i = 0, nics = d_qreg.getNumInstantiationConstants(q); i < nics;
       i++)
  {
    ce_vars.push_back(d_qreg.getInstantiationConstant(q, i));
  }
  // send the lemma
  d_qim.lemma(lem, InferenceId::QUANTIFIERS_CEGQI_CEX);
  // get the preprocessed form of the lemma we just sent
  std::vector<Node> skolems;
  std::vector<Node> skAsserts;
  Node ppLem =
      d_qstate.getValuation().getPreprocessedTerm(lem, skAsserts, skolems);
  std::vector<Node> lemp{ppLem};
  lemp.insert(lemp.end(), skAsserts.begin(), skAsserts.end());
  ppLem = NodeManager::currentNM()->mkAnd(lemp);
  Trace("cegqi-debug") << "Counterexample lemma (post-preprocess): " << ppLem
                       << std::endl;
  std::vector<Node> auxLems;
  CegInstantiator* cinst = getInstantiator(q);
  cinst->registerCounterexampleLemma(ppLem, ce_vars, auxLems);
  for (size_t i = 0, size = auxLems.size(); i < size; i++)
  {
    Trace("cegqi-debug") << "Auxiliary CE lemma " << i << " : " << auxLems[i]
                         << std::endl;
    d_qim.addPendingLemma(auxLems[i], InferenceId::QUANTIFIERS_CEGQI_CEX_AUX);
  }
}

bool InstStrategyCegqi::doCbqi(Node q)
{
  std::map<Node, CegHandledStatus>::iterator it = d_do_cbqi.find(q);
  if( it==d_do_cbqi.end() ){
    CegHandledStatus ret =
        CegInstantiator::isCbqiQuant(q, options().quantifiers.cegqiAll);
    Trace("cegqi-quant") << "doCbqi " << q << " returned " << ret << std::endl;
    d_do_cbqi[q] = ret;
    return ret != CEG_UNHANDLED;
  }
  return it->second != CEG_UNHANDLED;
}

void InstStrategyCegqi::process( Node q, Theory::Effort effort, int e ) {
  // If we are doing nested quantifier elimination, check if q was already
  // processed.
  if (processNestedQe(q, false))
  {
    // don't need to process this, since it has been reduced
    return;
  }
  // run the check
  if( e==0 ){
    CegInstantiator * cinst = getInstantiator( q );
    Trace("inst-alg") << "-> Run cegqi for " << q << std::endl;
    d_curr_quant = q;
    if( !cinst->check() ){
      d_incomplete_check = true;
    }
    d_curr_quant = Node::null();
  }

  // now, process the bounding lemmas for virtual terms
  NodeManager* nm = NodeManager::currentNM();
  VtsTermCache* vtc = d_treg.getVtsTermCache();
  if (e == 0)
  {
    // if the check was incomplete, process bounds at next effort level
    d_check_vts_lemma_lc = d_incomplete_check;
    // process the lower bound for free delta immediately
    Node delta = vtc->getVtsDelta(true, false);
    if (!delta.isNull())
    {
      if (!d_freeDeltaLb.get())
      {
        d_freeDeltaLb = true;
        Node zero = nm->mkConstReal(Rational(0));
        Node delta_lem = nm->mkNode(GT, delta, zero);
        d_qim.lemma(delta_lem, InferenceId::QUANTIFIERS_CEGQI_VTS_LB_DELTA);
      }
    }
  }
  else if (e == 1)
  {
    //minimize the free delta heuristically on demand
    if( d_check_vts_lemma_lc ){
      Trace("inst-alg") << "-> Minimize delta heuristic, for " << q << std::endl;
      d_check_vts_lemma_lc = false;
      d_small_const = nm->mkNode(MULT, d_small_const, d_small_const_multiplier);
      d_small_const = rewrite(d_small_const);
      //heuristic for now, until we know how to do nested quantification
      Node delta = vtc->getVtsDelta(true, false);
      if( !delta.isNull() ){
        Trace("quant-vts-debug") << "Delta lemma for " << d_small_const << std::endl;
        Node delta_lem_ub = nm->mkNode(LT, delta, d_small_const);
        d_qim.lemma(delta_lem_ub, InferenceId::QUANTIFIERS_CEGQI_VTS_UB_DELTA);
      }
      std::vector< Node > inf;
      vtc->getVtsTerms(inf, true, false, false);
      for (const Node& i : inf)
      {
        Trace("quant-vts-debug")
            << "Infinity lemma for " << i << " " << d_small_const << std::endl;
        Node inf_lem_lb = nm->mkNode(
            GT,
            i,
            nm->mkConstReal(Rational(1) / d_small_const.getConst<Rational>()));
        d_qim.lemma(inf_lem_lb, InferenceId::QUANTIFIERS_CEGQI_VTS_LB_INF);
      }
    }
  }
}

Node InstStrategyCegqi::getCounterexampleLiteral(Node q)
{
  std::map<Node, Node>::iterator it = d_ce_lit.find(q);
  if (it != d_ce_lit.end())
  {
    return it->second;
  }
  NodeManager * nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node g = sm->mkDummySkolem("g", nm->booleanType());
  // ensure that it is a SAT literal
  Node ceLit = d_qstate.getValuation().ensureLiteral(g);
  d_ce_lit[q] = ceLit;
  return ceLit;
}

CegInstantiator * InstStrategyCegqi::getInstantiator( Node q ) {
  std::map<Node, std::unique_ptr<CegInstantiator>>::iterator it =
      d_cinst.find(q);
  if( it==d_cinst.end() ){
    d_cinst[q].reset(
        new CegInstantiator(d_env, q, d_qstate, d_qim, d_qreg, d_treg));
    return d_cinst[q].get();
  }
  return it->second.get();
}

bool InstStrategyCegqi::processNestedQe(Node q, bool isPreregister)
{
  if (d_nestedQe != nullptr)
  {
    if (isPreregister)
    {
      // If at preregister, we are done if we have nested quantification.
      // We will process nested quantification.
      return NestedQe::hasNestedQuantification(q);
    }
    // if not a preregister, we process, which may trigger quantifier
    // elimination in subsolvers.
    std::vector<Node> lems;
    if (d_nestedQe->process(q, lems))
    {
      // add lemmas to process
      for (const Node& lem : lems)
      {
        d_qim.addPendingLemma(lem, InferenceId::QUANTIFIERS_CEGQI_NESTED_QE);
      }
      // don't need to process this, since it has been reduced
      return true;
    }
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
