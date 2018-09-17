/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **   This class is the entry point for both synthesis algorithms in Reynolds et al CAV 2015
 **
 **/
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"

#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( qe );
  d_last_inst_si = false;
}

CegInstantiation::~CegInstantiation(){ 
  delete d_conj;
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return !d_quantEngine->getTheoryEngine()->needCheck()
         && e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort CegInstantiation::needsModel(Theory::Effort e)
{
  return d_conj->isSingleInvocation() ? QEFFORT_STANDARD : QEFFORT_MODEL;
}

void CegInstantiation::check(Theory::Effort e, QEffort quant_e)
{
  // are we at the proper effort level?
  unsigned echeck =
      d_conj->isSingleInvocation() ? QEFFORT_STANDARD : QEFFORT_MODEL;
  if (quant_e != echeck)
  {
    return;
  }

  // if we are waiting to assign the conjecture, do it now
  if (!d_waiting_conj.isNull())
  {
    Node q = d_waiting_conj;
    Trace("cegqi-engine") << "--- Conjecture waiting to assign: " << q
                          << std::endl;
    d_waiting_conj = Node::null();
    if (!d_conj->isAssigned())
    {
      assignConjecture(q);
      // assign conjecture always uses the output channel, we return and
      // re-check here.
      return;
    }
  }

  Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---"
                        << std::endl;
  Trace("cegqi-engine-debug") << std::endl;
  bool active = false;
  bool value;
  if (d_quantEngine->getValuation().hasSatValue(d_conj->getConjecture(), value))
  {
    active = value;
  }
  else
  {
    Trace("cegqi-engine-debug")
        << "...no value for quantified formula." << std::endl;
  }
  Trace("cegqi-engine-debug")
      << "Current conjecture status : active : " << active << std::endl;
  if (active && d_conj->needsCheck())
  {
    checkConjecture(d_conj);
  }
  Trace("cegqi-engine")
      << "Finished Counterexample Guided Instantiation engine." << std::endl;
}

bool CegInstantiation::assignConjecture(Node q)
{
  if (d_conj->isAssigned())
  {
    return false;
  }
  Trace("cegqi-engine") << "--- Assign conjecture " << q << std::endl;
  if (options::sygusQePreproc())
  {
    // the following does quantifier elimination as a preprocess step
    // for "non-ground single invocation synthesis conjectures":
    //   exists f. forall xy. P[ f(x), x, y ]
    // We run quantifier elimination:
    //   exists y. P[ z, x, y ] ----> Q[ z, x ]
    // Where we replace the original conjecture with:
    //   exists f. forall x. Q[ f(x), x ]
    // For more details, see Example 6 of Reynolds et al. SYNT 2017.
    Node body = q[1];
    if (body.getKind() == NOT && body[0].getKind() == FORALL)
    {
      body = body[0][1];
    }
    NodeManager* nm = NodeManager::currentNM();
    Trace("cegqi-qep") << "Compute single invocation for " << q << "..."
                       << std::endl;
    quantifiers::SingleInvocationPartition sip;
    std::vector<Node> funcs;
    funcs.insert(funcs.end(), q[0].begin(), q[0].end());
    sip.init(funcs, body);
    Trace("cegqi-qep") << "...finished, got:" << std::endl;
    sip.debugPrint("cegqi-qep");

    if (!sip.isPurelySingleInvocation() && sip.isNonGroundSingleInvocation())
    {
      // create new smt engine to do quantifier elimination
      SmtEngine smt_qe(nm->toExprManager());
      smt_qe.setLogic(smt::currentSmtEngine()->getLogicInfo());
      Trace("cegqi-qep") << "Property is non-ground single invocation, run "
                            "QE to obtain single invocation."
                         << std::endl;
      // partition variables
      std::vector<Node> all_vars;
      sip.getAllVariables(all_vars);
      std::vector<Node> si_vars;
      sip.getSingleInvocationVariables(si_vars);
      std::vector<Node> qe_vars;
      std::vector<Node> nqe_vars;
      for (unsigned i = 0, size = all_vars.size(); i < size; i++)
      {
        Node v = all_vars[i];
        if (std::find(si_vars.begin(), si_vars.end(), v) == si_vars.end())
        {
          qe_vars.push_back(v);
        }
        else
        {
          nqe_vars.push_back(v);
        }
      }
      std::vector<Node> orig;
      std::vector<Node> subs;
      // skolemize non-qe variables
      for (unsigned i = 0, size = nqe_vars.size(); i < size; i++)
      {
        Node k = nm->mkSkolem(
            "k", nqe_vars[i].getType(), "qe for non-ground single invocation");
        orig.push_back(nqe_vars[i]);
        subs.push_back(k);
        Trace("cegqi-qep") << "  subs : " << nqe_vars[i] << " -> " << k
                           << std::endl;
      }
      std::vector<Node> funcs;
      sip.getFunctions(funcs);
      for (unsigned i = 0, size = funcs.size(); i < size; i++)
      {
        Node f = funcs[i];
        Node fi = sip.getFunctionInvocationFor(f);
        Node fv = sip.getFirstOrderVariableForFunction(f);
        Assert(!fi.isNull());
        orig.push_back(fi);
        Node k =
            nm->mkSkolem("k",
                         fv.getType(),
                         "qe for function in non-ground single invocation");
        subs.push_back(k);
        Trace("cegqi-qep") << "  subs : " << fi << " -> " << k << std::endl;
      }
      Node conj_se_ngsi = sip.getFullSpecification();
      Trace("cegqi-qep") << "Full specification is " << conj_se_ngsi
                         << std::endl;
      Node conj_se_ngsi_subs = conj_se_ngsi.substitute(
          orig.begin(), orig.end(), subs.begin(), subs.end());
      Assert(!qe_vars.empty());
      conj_se_ngsi_subs = nm->mkNode(EXISTS,
                                     nm->mkNode(BOUND_VAR_LIST, qe_vars),
                                     conj_se_ngsi_subs.negate());

      Trace("cegqi-qep") << "Run quantifier elimination on "
                         << conj_se_ngsi_subs << std::endl;
      Expr qe_res = smt_qe.doQuantifierElimination(
          conj_se_ngsi_subs.toExpr(), true, false);
      Trace("cegqi-qep") << "Result : " << qe_res << std::endl;

      // create single invocation conjecture
      Node qe_res_n = Node::fromExpr(qe_res);
      qe_res_n = qe_res_n.substitute(
          subs.begin(), subs.end(), orig.begin(), orig.end());
      if (!nqe_vars.empty())
      {
        qe_res_n =
            nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, nqe_vars), qe_res_n);
      }
      Assert(q.getNumChildren() == 3);
      qe_res_n = nm->mkNode(FORALL, q[0], qe_res_n, q[2]);
      Trace("cegqi-qep") << "Converted conjecture after QE : " << qe_res_n
                         << std::endl;
      qe_res_n = Rewriter::rewrite(qe_res_n);
      Node nq = qe_res_n;
      // must assert it is equivalent to the original
      Node lem = q.eqNode(nq);
      Trace("cegqi-lemma") << "Cegqi::Lemma : qe-preprocess : " << lem
                           << std::endl;
      d_quantEngine->getOutputChannel().lemma(lem);
      // we've reduced the original to a preprocessed version, return
      return false;
    }
  }
  d_conj->assign(q);
  return true;
}

void CegInstantiation::registerQuantifier(Node q)
{
  if (d_quantEngine->getOwner(q) == this)
  {  // && d_eval_axioms.find( q )==d_eval_axioms.end() ){
    if (!d_conj->isAssigned())
    {
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      if (options::sygusQePreproc())
      {
        d_waiting_conj = q;
      }
      else
      {
        // assign it now
        assignConjecture(q);
      }
    }else{
      Assert( d_conj->getEmbeddedConjecture()==q );
    }
  }else{
    Trace("cegqi-debug") << "Register quantifier : " << q << std::endl;
  }
}

Node CegInstantiation::getNextDecisionRequest( unsigned& priority ) {
  if( d_conj->isAssigned() ){
    Node dec_req = d_conj->getNextDecisionRequest( priority );
    if( !dec_req.isNull() ){
      Trace("cegqi-debug") << "CEGQI : Decide next on : " << dec_req << "..." << std::endl;
      return dec_req;
    }
  }
  return Node::null();
}

void CegInstantiation::checkConjecture(CegConjecture* conj)
{
  Node q = conj->getEmbeddedConjecture();
  Node aq = conj->getConjecture();
  if( Trace.isOn("cegqi-engine-debug") ){
    conj->debugPrint("cegqi-engine-debug");
    Trace("cegqi-engine-debug") << std::endl;
  }

  if( !conj->needsRefinement() ){
    Trace("cegqi-engine-debug") << "Do conjecture check..." << std::endl;
    if (conj->isSingleInvocation())
    {
      std::vector<Node> clems;
      conj->doSingleInvCheck(clems);
      if (!clems.empty())
      {
        d_last_inst_si = true;
        for (const Node& lem : clems)
        {
          Trace("cegqi-lemma")
              << "Cegqi::Lemma : single invocation instantiation : " << lem
              << std::endl;
          d_quantEngine->addLemma(lem);
        }
        d_statistics.d_cegqi_si_lemmas += clems.size();
        Trace("cegqi-engine") << "  ...try single invocation." << std::endl;
      }
      else
      {
        // This can happen for non-monotonic instantiation strategies. We
        // set --cbqi-full to ensure that for most strategies (e.g. BV), we
        // are using a monotonic strategy.
        Trace("cegqi-warn")
            << "  ...FAILED to add cbqi instantiation for single invocation!"
            << std::endl;
      }
      return;
    }

    Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
    std::vector<Node> cclems;
    conj->doCheck(cclems);
    bool addedLemma = false;
    for (const Node& lem : cclems)
    {
      d_last_inst_si = false;
      Trace("cegqi-lemma") << "Cegqi::Lemma : counterexample : " << lem
                           << std::endl;
      if (d_quantEngine->addLemma(lem))
      {
        ++(d_statistics.d_cegqi_lemmas_ce);
        addedLemma = true;
      }else{
        // this may happen if we eagerly unfold, simplify to true
        Trace("cegqi-engine-debug")
            << "  ...FAILED to add candidate!" << std::endl;
      }
    }
    if (addedLemma)
    {
      Trace("cegqi-engine") << "  ...check for counterexample." << std::endl;
    }else{
      if (conj->needsRefinement())
      {
        // immediately go to refine candidate
        checkConjecture(conj);
        return;
      }
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    std::vector< Node > rlems;
    conj->doRefine( rlems );
    bool addedLemma = false;
    for( unsigned i=0; i<rlems.size(); i++ ){
      Node lem = rlems[i];
      Trace("cegqi-lemma") << "Cegqi::Lemma : candidate refinement : " << lem << std::endl;
      bool res = d_quantEngine->addLemma( lem );
      if( res ){
        ++(d_statistics.d_cegqi_lemmas_refine);
        conj->incrementRefineCount();
        addedLemma = true;
      }else{
        Trace("cegqi-warn") << "  ...FAILED to add refinement!" << std::endl;
      }
    }
    if( addedLemma ){
      Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
    }
  }
}

void CegInstantiation::printSynthSolution( std::ostream& out ) {
  if( d_conj->isAssigned() )
  {
    d_conj->printSynthSolution( out, d_last_inst_si );
  }
  else
  {
    Assert( false );
  }
}

void CegInstantiation::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  if (d_conj->isAssigned())
  {
    d_conj->getSynthSolutions(sol_map, d_last_inst_si);
  }
}

void CegInstantiation::preregisterAssertion( Node n ) {
  //check if it sygus conjecture
  if( QuantAttributes::checkSygusConjecture( n ) ){
    //this is a sygus conjecture
    Trace("cegqi") << "Preregister sygus conjecture : " << n << std::endl;
    d_conj->preregisterConjecture( n );
  }
}

CegInstantiation::Statistics::Statistics()
    : d_cegqi_lemmas_ce("CegInstantiation::cegqi_lemmas_ce", 0),
      d_cegqi_lemmas_refine("CegInstantiation::cegqi_lemmas_refine", 0),
      d_cegqi_si_lemmas("CegInstantiation::cegqi_lemmas_si", 0),
      d_solutions("CegConjecture::solutions", 0),
      d_candidate_rewrites_print("CegConjecture::candidate_rewrites_print", 0),
      d_candidate_rewrites("CegConjecture::candidate_rewrites", 0)

{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->registerStat(&d_solutions);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites);
}

CegInstantiation::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites);
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
