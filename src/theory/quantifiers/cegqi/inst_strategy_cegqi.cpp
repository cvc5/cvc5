/*********************                                                        */
/*! \file inst_strategy_cegqi.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation strategies
 **/
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

InstRewriterCegqi::InstRewriterCegqi(InstStrategyCegqi* p)
    : InstantiationRewriter(), d_parent(p)
{
}

TrustNode InstRewriterCegqi::rewriteInstantiation(Node q,
                                                  std::vector<Node>& terms,
                                                  Node inst,
                                                  bool doVts)
{
  return d_parent->rewriteInstantiation(q, terms, inst, doVts);
}

InstStrategyCegqi::InstStrategyCegqi(QuantifiersEngine* qe,
                                     QuantifiersState& qs,
                                     QuantifiersInferenceManager& qim,
                                     QuantifiersRegistry& qr)
    : QuantifiersModule(qs, qim, qr, qe),
      d_irew(new InstRewriterCegqi(this)),
      d_cbqi_set_quant_inactive(false),
      d_incomplete_check(false),
      d_added_cbqi_lemma(qs.getUserContext()),
      d_vtsCache(new VtsTermCache(qe)),
      d_bv_invert(nullptr)
{
  d_small_const =
      NodeManager::currentNM()->mkConst(Rational(1) / Rational(1000000));
  d_check_vts_lemma_lc = false;
  if (options::cegqiBv())
  {
    // if doing instantiation for BV, need the inverter class
    d_bv_invert.reset(new BvInverter);
  }
  if (options::cegqiNestedQE())
  {
    d_nestedQe.reset(new NestedQe(qs.getUserContext()));
  }
}

InstStrategyCegqi::~InstStrategyCegqi() {}

bool InstStrategyCegqi::needsCheck(Theory::Effort e)
{
  return e>=Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstStrategyCegqi::needsModel(Theory::Effort e)
{
  size_t nquant = d_quantEngine->getModel()->getNumAssertedQuantifiers();
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
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
    Node ceBody = d_quantEngine->getTermUtil()->getInstConstantBody( q );
    if( !ceBody.isNull() ){
      //add counterexample lemma
      Node lem = NodeManager::currentNM()->mkNode( OR, ceLit.negate(), ceBody.negate() );
      //require any decision on cel to be phase=true
      d_qim.addPendingPhaseRequirement(ceLit, true);
      Debug("cegqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
      //add counterexample lemma
      lem = Rewriter::rewrite( lem );
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
        d_quantEngine->getOutputChannel().lemma(dep_lemma);
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
      d_dstrat[q].reset(
          new DecisionStrategySingleton("CexLiteral",
                                        ceLit,
                                        d_qstate.getSatContext(),
                                        d_quantEngine->getValuation()));
      dlds = d_dstrat[q].get();
    }
    else
    {
      dlds = itds->second.get();
    }
    // it is appended to the list of strategies
    d_quantEngine->getDecisionManager()->registerStrategy(
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
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
    if( doCbqi( q ) ){
      if( d_quantEngine->getModel()->isQuantifierActive( q ) ){
        d_active_quant[q] = true;
        Debug("cegqi-debug") << "Check quantified formula " << q << "..." << std::endl;
        Node cel = getCounterexampleLiteral(q);
        bool value;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          Debug("cegqi-debug") << "...CE Literal has value " << value << std::endl;
          if( !value ){
            if( d_quantEngine->getValuation().isDecision( cel ) ){
              Trace("cegqi-warn") << "CBQI WARNING: Bad decision on CE Literal." << std::endl;
            }else{
              Trace("cegqi") << "Inactive : " << q << std::endl;
              d_quantEngine->getModel()->setQuantifierActive( q, false );
              d_cbqi_set_quant_inactive = true;
              d_active_quant.erase( q );
            }
          }
        }else{
          Debug("cegqi-debug") << "...CE Literal does not have value " << std::endl;
        }
      }
    }
  }

  //refinement: only consider innermost active quantified formulas
  if( options::cegqiInnermost() ){
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
    if( Trace.isOn("cegqi-engine") ){
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
    if( Trace.isOn("cegqi-engine") ){
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

bool InstStrategyCegqi::checkComplete()
{
  if( ( !options::cegqiSat() && d_cbqi_set_quant_inactive ) || d_incomplete_check ){
    return false;
  }else{
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
TrustNode InstStrategyCegqi::rewriteInstantiation(Node q,
                                                  std::vector<Node>& terms,
                                                  Node inst,
                                                  bool doVts)
{
  Node prevInst = inst;
  if (doVts)
  {
    // do virtual term substitution
    inst = Rewriter::rewrite(inst);
    Trace("quant-vts-debug") << "Rewrite vts symbols in " << inst << std::endl;
    inst = d_vtsCache->rewriteVtsSymbols(inst);
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
  TermUtil* tutil = d_quantEngine->getTermUtil();
  for (unsigned i = 0, nics = tutil->getNumInstantiationConstants(q); i < nics;
       i++)
  {
    ce_vars.push_back(tutil->getInstantiationConstant(q, i));
  }
  // send the lemma
  d_quantEngine->getOutputChannel().lemma(lem);
  // get the preprocessed form of the lemma we just sent
  std::vector<Node> skolems;
  std::vector<Node> skAsserts;
  Node ppLem = d_quantEngine->getValuation().getPreprocessedTerm(
      lem, skAsserts, skolems);
  std::vector<Node> lemp{ppLem};
  lemp.insert(lemp.end(), skAsserts.begin(), skAsserts.end());
  ppLem = NodeManager::currentNM()->mkAnd(lemp);
  Trace("cegqi-debug") << "Counterexample lemma (post-preprocess): " << ppLem
                       << std::endl;
  std::vector<Node> auxLems;
  CegInstantiator* cinst = getInstantiator(q);
  cinst->registerCounterexampleLemma(ppLem, ce_vars, auxLems);
  for (unsigned i = 0, size = auxLems.size(); i < size; i++)
  {
    Trace("cegqi-debug") << "Auxiliary CE lemma " << i << " : " << auxLems[i]
                         << std::endl;
    d_qim.addPendingLemma(auxLems[i]);
  }
}

bool InstStrategyCegqi::doCbqi(Node q)
{
  std::map<Node, CegHandledStatus>::iterator it = d_do_cbqi.find(q);
  if( it==d_do_cbqi.end() ){
    CegHandledStatus ret = CegInstantiator::isCbqiQuant(q, d_quantEngine);
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
  if( e==0 ){
    CegInstantiator * cinst = getInstantiator( q );
    Trace("inst-alg") << "-> Run cegqi for " << q << std::endl;
    d_curr_quant = q;
    if( !cinst->check() ){
      d_incomplete_check = true;
      d_check_vts_lemma_lc = true;
    }
    d_curr_quant = Node::null();
  }else if( e==1 ){
    //minimize the free delta heuristically on demand
    if( d_check_vts_lemma_lc ){
      Trace("inst-alg") << "-> Minimize delta heuristic, for " << q << std::endl;
      d_check_vts_lemma_lc = false;
      d_small_const = NodeManager::currentNM()->mkNode( MULT, d_small_const, d_small_const );
      d_small_const = Rewriter::rewrite( d_small_const );
      //heuristic for now, until we know how to do nested quantification
      Node delta = d_vtsCache->getVtsDelta(true, false);
      if( !delta.isNull() ){
        Trace("quant-vts-debug") << "Delta lemma for " << d_small_const << std::endl;
        Node delta_lem_ub = NodeManager::currentNM()->mkNode( LT, delta, d_small_const );
        d_quantEngine->getOutputChannel().lemma( delta_lem_ub );
      }
      std::vector< Node > inf;
      d_vtsCache->getVtsTerms(inf, true, false, false);
      for( unsigned i=0; i<inf.size(); i++ ){
        Trace("quant-vts-debug") << "Infinity lemma for " << inf[i] << " " << d_small_const << std::endl;
        Node inf_lem_lb = NodeManager::currentNM()->mkNode( GT, inf[i], NodeManager::currentNM()->mkConst( Rational(1)/d_small_const.getConst<Rational>() ) );
        d_quantEngine->getOutputChannel().lemma( inf_lem_lb );
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
  Node g = nm->mkSkolem("g", nm->booleanType());
  // ensure that it is a SAT literal
  Node ceLit = d_quantEngine->getValuation().ensureLiteral(g);
  d_ce_lit[q] = ceLit;
  return ceLit;
}

bool InstStrategyCegqi::doAddInstantiation( std::vector< Node >& subs ) {
  Assert(!d_curr_quant.isNull());
  //if doing partial quantifier elimination, record the instantiation and set the incomplete flag instead of sending instantiation lemma
  if( d_quantEngine->getQuantAttributes()->isQuantElimPartial( d_curr_quant ) ){
    d_cbqi_set_quant_inactive = true;
    d_incomplete_check = true;
    d_quantEngine->getInstantiate()->recordInstantiation(
        d_curr_quant, subs, false, false);
    return true;
  }else{
    //check if we need virtual term substitution (if used delta or infinity)
    bool used_vts = d_vtsCache->containsVtsTerm(subs, false);
    if (d_quantEngine->getInstantiate()->addInstantiation(
            d_curr_quant, subs, false, false, used_vts))
    {
      ++(d_quantEngine->d_statistics.d_instantiations_cbqi);
      //d_added_inst.insert( d_curr_quant );
      return true;
    }else{
      //this should never happen for monotonic selection strategies
      Trace("cegqi-warn") << "WARNING: Existing instantiation" << std::endl;
      return false;
    }
  }
}

bool InstStrategyCegqi::addPendingLemma(Node lem) const
{
  return d_qim.addPendingLemma(lem);
}

CegInstantiator * InstStrategyCegqi::getInstantiator( Node q ) {
  std::map<Node, std::unique_ptr<CegInstantiator>>::iterator it =
      d_cinst.find(q);
  if( it==d_cinst.end() ){
    d_cinst[q].reset(new CegInstantiator(q, this));
    return d_cinst[q].get();
  }
  return it->second.get();
}

VtsTermCache* InstStrategyCegqi::getVtsTermCache() const
{
  return d_vtsCache.get();
}

BvInverter* InstStrategyCegqi::getBvInverter() const
{
  return d_bv_invert.get();
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
        d_qim.addPendingLemma(lem);
      }
      // don't need to process this, since it has been reduced
      return true;
    }
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
