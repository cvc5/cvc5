/*********************                                                        */
/*! \file ce_guided_single_inv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"

#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegSingleInv::CegSingleInv(QuantifiersEngine* qe, SynthConjecture* p)
    : d_qe(qe),
      d_parent(p),
      d_sip(new SingleInvocationPartition),
      d_sol(new CegSingleInvSol(qe)),
      d_isSolved(false),
      d_single_invocation(false)
{

}

CegSingleInv::~CegSingleInv()
{
  delete d_sol;  // (new CegSingleInvSol(qe)),
  delete d_sip;  // d_sip(new SingleInvocationPartition),
}

void CegSingleInv::initialize(Node q)
{
  // can only register one quantified formula with this
  Assert(d_quant.isNull());
  d_quant = q;
  d_simp_quant = q;
  Trace("sygus-si") << "CegSingleInv::initialize : " << q << std::endl;
  // infer single invocation-ness

  // get the variables
  std::vector< Node > progs;
  std::map< Node, std::vector< Node > > prog_vars;
  for (const Node& sf : q[0])
  {
    progs.push_back( sf );
    Node sfvl = CegGrammarConstructor::getSygusVarList(sf);
    if (!sfvl.isNull())
    {
      for (const Node& sfv : sfvl)
      {
        prog_vars[sf].push_back(sfv);
      }
    }
  }
  // compute single invocation partition
  Node qq;
  if (q[1].getKind() == NOT && q[1][0].getKind() == FORALL)
  {
    qq = q[1][0][1];
  }
  else
  {
    qq = TermUtil::simpleNegate(q[1]);
  }
  // process the single invocation-ness of the property
  if (!d_sip->init(progs, qq))
  {
    Trace("sygus-si") << "...not single invocation (type mismatch)"
                      << std::endl;
    return;
  }
  Trace("sygus-si") << "- Partitioned to single invocation parts : "
                    << std::endl;
  d_sip->debugPrint("sygus-si");

  // map from program to bound variables
  std::vector<Node> funcs;
  d_sip->getFunctions(funcs);
  for (unsigned j = 0, size = funcs.size(); j < size; j++)
  {
    Assert(std::find(progs.begin(), progs.end(), funcs[j]) != progs.end());
    d_prog_to_sol_index[funcs[j]] = j;
  }

  // check if it is single invocation
  if (d_sip->isPurelySingleInvocation())
  {
    // We are fully single invocation, set single invocation if we haven't
    // disabled single invocation techniques.
    if (options::cegqiSingleInvMode() != options::CegqiSingleInvMode::NONE)
    {
      d_single_invocation = true;
      return;
    }
  }
  // We are processing without single invocation techniques, now check if
  // we should fix an invariant template (post-condition strengthening or
  // pre-condition weakening).
  options::SygusInvTemplMode tmode = options::sygusInvTemplMode();
  if (tmode != options::SygusInvTemplMode::NONE)
  {
    // currently only works for single predicate synthesis
    if (q[0].getNumChildren() > 1 || !q[0][0].getType().isPredicate())
    {
      tmode = options::SygusInvTemplMode::NONE;
    }
    else if (!options::sygusInvTemplWhenSyntax())
    {
      // only use invariant templates if no syntactic restrictions
      if (CegGrammarConstructor::hasSyntaxRestrictions(q))
      {
        tmode = options::SygusInvTemplMode::NONE;
      }
    }
  }

  if (tmode == options::SygusInvTemplMode::NONE)
  {
    // not processing invariant templates
    return;
  }
  // if we are doing invariant templates, then construct the template
  Trace("sygus-si") << "- Do transition inference..." << std::endl;
  d_ti[q].process(qq, q[0][0]);
  Trace("cegqi-inv") << std::endl;
  Node prog = d_ti[q].getFunction();
  if (!d_ti[q].isComplete())
  {
    // the invariant could not be inferred
    return;
  }
  Assert(prog == q[0][0]);
  NodeManager* nm = NodeManager::currentNM();
  // map the program back via non-single invocation map
  std::vector<Node> prog_templ_vars;
  d_ti[q].getVariables(prog_templ_vars);
  d_trans_pre[prog] = d_ti[q].getPreCondition();
  d_trans_post[prog] = d_ti[q].getPostCondition();
  Trace("cegqi-inv") << "   precondition : " << d_trans_pre[prog] << std::endl;
  Trace("cegqi-inv") << "  postcondition : " << d_trans_post[prog] << std::endl;
  std::vector<Node> sivars;
  d_sip->getSingleInvocationVariables(sivars);
  Node invariant = d_sip->getFunctionInvocationFor(prog);
  if (invariant.isNull())
  {
    // the conjecture did not have an instance of the invariant
    // (e.g. it is trivially true/false).
    return;
  }
  invariant = invariant.substitute(sivars.begin(),
                                   sivars.end(),
                                   prog_templ_vars.begin(),
                                   prog_templ_vars.end());
  Trace("cegqi-inv") << "      invariant : " << invariant << std::endl;

  // store simplified version of quantified formula
  d_simp_quant = d_sip->getFullSpecification();
  std::vector<Node> new_bv;
  for( const Node& v : sivars )
  {
    new_bv.push_back(nm->mkBoundVar(v.getType()));
  }
  d_simp_quant = d_simp_quant.substitute(
      sivars.begin(), sivars.end(), new_bv.begin(), new_bv.end());
  Assert(q[1].getKind() == NOT && q[1][0].getKind() == FORALL);
  for (const Node& v : q[1][0][0])
  {
    new_bv.push_back(v);
  }
  d_simp_quant =
      nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, new_bv), d_simp_quant)
          .negate();
  d_simp_quant = Rewriter::rewrite(d_simp_quant);
  d_simp_quant = nm->mkNode(FORALL, q[0], d_simp_quant, q[2]);
  Trace("sygus-si") << "Rewritten quantifier : " << d_simp_quant << std::endl;

  // construct template argument
  d_templ_arg[prog] = nm->mkSkolem("I", invariant.getType());

  // construct template
  Node templ;
  if (options::sygusInvAutoUnfold())
  {
    if (d_ti[q].isComplete())
    {
      Trace("cegqi-inv-auto-unfold")
          << "Automatic deterministic unfolding... " << std::endl;
      // auto-unfold
      DetTrace dt;
      int init_dt = d_ti[q].initializeTrace(dt);
      if (init_dt == 0)
      {
        Trace("cegqi-inv-auto-unfold") << "  Init : ";
        dt.print("cegqi-inv-auto-unfold");
        Trace("cegqi-inv-auto-unfold") << std::endl;
        unsigned counter = 0;
        unsigned status = 0;
        while (counter < 100 && status == 0)
        {
          status = d_ti[q].incrementTrace(dt);
          counter++;
          Trace("cegqi-inv-auto-unfold") << "  #" << counter << " : ";
          dt.print("cegqi-inv-auto-unfold");
          Trace("cegqi-inv-auto-unfold")
              << "...status = " << status << std::endl;
        }
        if (status == 1)
        {
          // we have a trivial invariant
          templ = d_ti[q].constructFormulaTrace(dt);
          Trace("cegqi-inv") << "By finite deterministic terminating trace, a "
                                "solution invariant is : "
                             << std::endl;
          Trace("cegqi-inv") << "   " << templ << std::endl;
          // this should be unnecessary
          templ = nm->mkNode(AND, templ, d_templ_arg[prog]);
        }
      }
      else
      {
        Trace("cegqi-inv-auto-unfold") << "...failed initialize." << std::endl;
      }
    }
  }
  Trace("cegqi-inv") << "Make the template... " << tmode << " " << templ
                     << std::endl;
  if (templ.isNull())
  {
    if (tmode == options::SygusInvTemplMode::PRE)
    {
      templ = nm->mkNode(OR, d_trans_pre[prog], d_templ_arg[prog]);
    }
    else
    {
      Assert(tmode == options::SygusInvTemplMode::POST);
      templ = nm->mkNode(AND, d_trans_post[prog], d_templ_arg[prog]);
    }
  }
  Trace("cegqi-inv") << "       template (pre-substitution) : " << templ
                     << std::endl;
  Assert(!templ.isNull());
  // subsitute the template arguments
  Assert(prog_templ_vars.size() == prog_vars[prog].size());
  templ = templ.substitute(prog_templ_vars.begin(),
                           prog_templ_vars.end(),
                           prog_vars[prog].begin(),
                           prog_vars[prog].end());
  Trace("cegqi-inv") << "       template : " << templ << std::endl;
  d_templ[prog] = templ;
}

void CegSingleInv::finishInit(bool syntaxRestricted)
{
  Trace("sygus-si-debug") << "Single invocation: finish init" << std::endl;
  // do not do single invocation if grammar is restricted and
  // options::CegqiSingleInvMode::ALL is not enabled
  if (options::cegqiSingleInvMode() == options::CegqiSingleInvMode::USE
      && d_single_invocation && syntaxRestricted)
  {
    d_single_invocation = false;
    Trace("sygus-si") << "...grammar is restricted, do not use single invocation techniques." << std::endl;
  }

  // we now have determined whether we will do single invocation techniques
  if (!d_single_invocation)
  {
    d_single_inv = Node::null();
    Trace("sygus-si") << "Formula is not single invocation." << std::endl;
    if (options::cegqiSingleInvAbort())
    {
      std::stringstream ss;
      ss << "Property is not handled by single invocation." << std::endl;
      throw LogicException(ss.str());
    }
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  d_single_inv = d_sip->getSingleInvocation();
  d_single_inv = TermUtil::simpleNegate(d_single_inv);
  std::vector<Node> func_vars;
  d_sip->getFunctionVariables(func_vars);
  if (!func_vars.empty())
  {
    Node pbvl = nm->mkNode(BOUND_VAR_LIST, func_vars);
    // make the single invocation conjecture
    d_single_inv = nm->mkNode(FORALL, pbvl, d_single_inv);
  }
  // now, introduce the skolems
  std::vector<Node> sivars;
  d_sip->getSingleInvocationVariables(sivars);
  for (unsigned i = 0, size = sivars.size(); i < size; i++)
  {
    Node v = NodeManager::currentNM()->mkSkolem(
        "a", sivars[i].getType(), "single invocation arg");
    d_single_inv_arg_sk.push_back(v);
  }
  d_single_inv = d_single_inv.substitute(sivars.begin(),
                                         sivars.end(),
                                         d_single_inv_arg_sk.begin(),
                                         d_single_inv_arg_sk.end());
  Trace("sygus-si") << "Single invocation formula is : " << d_single_inv
                    << std::endl;
  // check whether we can handle this quantified formula
  CegHandledStatus status = CEG_HANDLED;
  if (d_single_inv.getKind() == FORALL)
  {
    // if the conjecture is not trivially solvable
    if (!solveTrivial(d_single_inv))
    {
      status = CegInstantiator::isCbqiQuant(d_single_inv);
    }
  }
  Trace("sygus-si") << "CegHandledStatus is " << status << std::endl;
  if (status < CEG_HANDLED)
  {
    Trace("sygus-si") << "...do not invoke single invocation techniques since "
                         "the quantified formula does not have a handled "
                         "counterexample-guided instantiation strategy!"
                      << std::endl;
    d_single_invocation = false;
    d_single_inv = Node::null();
  }
}

bool CegSingleInv::solve()
{
  if (d_single_inv.isNull())
  {
    // not using single invocation techniques
    return false;
  }
  if (d_isSolved)
  {
    // already solved, probably via a call to solveTrivial.
    return true;
  }
  Trace("sygus-si") << "Solve using single invocation..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // Mark the quantified formula with the quantifier elimination attribute to
  // ensure its structure is preserved in the query below.
  Node siq = d_single_inv;
  if (siq.getKind() == FORALL)
  {
    Node n_attr =
        nm->mkSkolem("qe_si",
                     nm->booleanType(),
                     "Auxiliary variable for qe attr for single invocation.");
    QuantElimAttribute qea;
    n_attr.setAttribute(qea, true);
    n_attr = nm->mkNode(INST_ATTRIBUTE, n_attr);
    n_attr = nm->mkNode(INST_PATTERN_LIST, n_attr);
    siq = nm->mkNode(FORALL, siq[0], siq[1], n_attr);
  }
  // solve the single invocation conjecture using a fresh copy of SMT engine
  SmtEngine siSmt(nm->toExprManager());
  siSmt.setLogic(smt::currentSmtEngine()->getLogicInfo());
  siSmt.assertFormula(siq.toExpr());
  Result r = siSmt.checkSat();
  Trace("sygus-si") << "Result: " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
  {
    // conjecture is infeasible or unknown
    return false;
  }
  // now, get the instantiations
  std::vector<Expr> qs;
  siSmt.getInstantiatedQuantifiedFormulas(qs);
  Assert(qs.size() <= 1);
  // track the instantiations, as solution construction is based on this
  Trace("sygus-si") << "#instantiated quantified formulas=" << qs.size()
                    << std::endl;
  d_inst.clear();
  d_instConds.clear();
  for (const Expr& q : qs)
  {
    TNode qn = Node::fromExpr(q);
    Assert(qn.getKind() == FORALL);
    std::vector<std::vector<Expr> > tvecs;
    siSmt.getInstantiationTermVectors(q, tvecs);
    Trace("sygus-si") << "#instantiations of " << q << "=" << tvecs.size()
                      << std::endl;
    std::vector<Node> vars;
    for (const Node& v : qn[0])
    {
      vars.push_back(v);
    }
    Node body = qn[1];
    for (unsigned i = 0, ninsts = tvecs.size(); i < ninsts; i++)
    {
      std::vector<Expr>& tvi = tvecs[i];
      std::vector<Node> inst;
      for (const Expr& t : tvi)
      {
        inst.push_back(Node::fromExpr(t));
      }
      Trace("sygus-si") << "  Instantiation: " << inst << std::endl;
      d_inst.push_back(inst);
      Assert(inst.size() == vars.size());
      Node ilem =
          body.substitute(vars.begin(), vars.end(), inst.begin(), inst.end());
      ilem = Rewriter::rewrite(ilem);
      d_instConds.push_back(ilem);
      Trace("sygus-si") << "  Instantiation Lemma: " << ilem << std::endl;
    }
  }
  d_isSolved = true;
  return true;
}

//TODO: use term size?
struct sortSiInstanceIndices {
  CegSingleInv* d_ccsi;
  int d_i;
  bool operator() (unsigned i, unsigned j) {
    if( d_ccsi->d_inst[i][d_i].isConst() && !d_ccsi->d_inst[j][d_i].isConst() ){
      return true;
    }else{
      return false;
    }
  }
};

Node CegSingleInv::getSolution(unsigned sol_index,
                               TypeNode stn,
                               int& reconstructed,
                               bool rconsSygus)
{
  Assert(d_sol != NULL);
  const DType& dt = stn.getDType();
  Node varList = dt.getSygusVarList();
  Node prog = d_quant[0][sol_index];
  std::vector< Node > vars;
  Node s;
  // If it is unconstrained: either the variable does not appear in the
  // conjecture or the conjecture can be solved without a single instantiation.
  if (d_prog_to_sol_index.find(prog) == d_prog_to_sol_index.end()
      || d_inst.empty())
  {
    Trace("csi-sol") << "Get solution for (unconstrained) " << prog << std::endl;
    s = d_qe->getTermEnumeration()->getEnumerateTerm(dt.getSygusType(), 0);
  }
  else
  {
    Trace("csi-sol") << "Get solution for " << prog << ", with skolems : ";
    sol_index = d_prog_to_sol_index[prog];
    d_sol->d_varList.clear();
    Assert(d_single_inv_arg_sk.size() == varList.getNumChildren());
    for( unsigned i=0; i<d_single_inv_arg_sk.size(); i++ ){
      Trace("csi-sol") << d_single_inv_arg_sk[i] << " ";
      vars.push_back( d_single_inv_arg_sk[i] );
      d_sol->d_varList.push_back( varList[i] );
    }
    Trace("csi-sol") << std::endl;

    //construct the solution
    Trace("csi-sol") << "Sort solution return values " << sol_index << std::endl;
    std::vector< unsigned > indices;
    for (unsigned i = 0, ninst = d_inst.size(); i < ninst; i++)
    {
      indices.push_back(i);
    }
    Assert(!indices.empty());
    // We are constructing an ITE based on the list of instantiations. We
    // sort this list based on heuristic. Currently, we do all constant values
    // first since this leads to simpler conditions. Notice that we only allow
    // sorting if we have a single variable, since the correctness of
    // Proposition 1 of Reynolds et al CAV 2015 for the case of multiple
    // functions-to-synthesize requires that the instantiations come in the
    // same order for all functions. Thus, we cannot decide on an order for
    // instantiations independently, since this may lead to incorrect solutions.
    bool allowSort = (d_quant[0].getNumChildren() == 1);
    if (allowSort)
    {
      sortSiInstanceIndices ssii;
      ssii.d_ccsi = this;
      ssii.d_i = sol_index;
      std::sort(indices.begin(), indices.end(), ssii);
    }
    Trace("csi-sol") << "Construct solution" << std::endl;
    std::reverse(indices.begin(), indices.end());
    s = d_inst[indices[0]][sol_index];
    // it is an ITE chain whose conditions are the instantiations
    NodeManager* nm = NodeManager::currentNM();
    for (unsigned j = 1, nindices = indices.size(); j < nindices; j++)
    {
      unsigned uindex = indices[j];
      Node cond = d_instConds[uindex];
      cond = TermUtil::simpleNegate(cond);
      s = nm->mkNode(ITE, cond, d_inst[uindex][sol_index], s);
    }
    Assert(vars.size() == d_sol->d_varList.size());
    s = s.substitute( vars.begin(), vars.end(), d_sol->d_varList.begin(), d_sol->d_varList.end() );
  }
  d_orig_solution = s;

  //simplify the solution using the extended rewriter
  Trace("csi-sol") << "Solution (pre-simplification): " << d_orig_solution << std::endl;
  s = d_qe->getTermDatabaseSygus()->getExtRewriter()->extendedRewrite(s);
  Trace("csi-sol") << "Solution (post-simplification): " << s << std::endl;
  return reconstructToSyntax( s, stn, reconstructed, rconsSygus );
}

Node CegSingleInv::reconstructToSyntax(Node s,
                                       TypeNode stn,
                                       int& reconstructed,
                                       bool rconsSygus)
{
  d_solution = s;
  const DType& dt = stn.getDType();

  //reconstruct the solution into sygus if necessary
  reconstructed = 0;
  if (options::cegqiSingleInvReconstruct()
          != options::CegqiSingleInvRconsMode::NONE
      && !dt.getSygusAllowAll() && !stn.isNull() && rconsSygus)
  {
    d_sol->preregisterConjecture( d_orig_conjecture );
    int enumLimit = -1;
    if (options::cegqiSingleInvReconstruct()
        == options::CegqiSingleInvRconsMode::TRY)
    {
      enumLimit = 0;
    }
    else if (options::cegqiSingleInvReconstruct()
             == options::CegqiSingleInvRconsMode::ALL_LIMIT)
    {
      enumLimit = options::cegqiSingleInvReconstructLimit();
    }
    d_sygus_solution =
        d_sol->reconstructSolution(s, stn, reconstructed, enumLimit);
    if( reconstructed==1 ){
      Trace("csi-sol") << "Solution (post-reconstruction into Sygus): " << d_sygus_solution << std::endl;
    }
  }else{
    Trace("csi-sol") << "Post-process solution..." << std::endl;
    Node prev = d_solution;
    d_solution =
        d_qe->getTermDatabaseSygus()->getExtRewriter()->extendedRewrite(
            d_solution);
    if( prev!=d_solution ){
      Trace("csi-sol") << "Solution (after post process) : " << d_solution << std::endl;
    }
  }

  // debug solution
  if (!d_sol->debugSolution(d_solution))
  {
    // This can happen if we encountered free variables in either the
    // instantiation terms, or in the instantiation lemmas after postprocessing.
    // In this case, we fail, since the solution is not valid.
    Trace("csi-sol") << "FAIL : solution " << d_solution
                     << " contains free constants." << std::endl;
    reconstructed = -1;
  }
  if( Trace.isOn("cegqi-stats") ){
    int tsize, itesize;
    tsize = 0;itesize = 0;
    d_sol->debugTermSize( d_orig_solution, tsize, itesize );
    Trace("cegqi-stats") << tsize << " " << itesize << " ";
    tsize = 0;itesize = 0;
    d_sol->debugTermSize( d_solution, tsize, itesize );
    Trace("cegqi-stats") << tsize << " " << itesize << " ";
    if( !d_sygus_solution.isNull() ){
      tsize = 0;itesize = 0;
      d_sol->debugTermSize( d_sygus_solution, tsize, itesize );
      Trace("cegqi-stats") << tsize << " - ";
    }else{
      Trace("cegqi-stats") << "null ";
    }
    Trace("cegqi-stats") << std::endl;
  }
  Node sol;
  if( reconstructed==1 ){
    sol = d_sygus_solution;
  }else if( reconstructed==-1 ){
    return Node::null();
  }else{
    sol = d_solution;
  }
  //make into lambda
  if( !dt.getSygusVarList().isNull() ){
    Node varList = dt.getSygusVarList();
    return NodeManager::currentNM()->mkNode( LAMBDA, varList, sol );
  }else{
    return sol;
  }
}

void CegSingleInv::preregisterConjecture(Node q) { d_orig_conjecture = q; }

bool CegSingleInv::solveTrivial(Node q)
{
  Assert(!d_isSolved);
  Assert(d_inst.empty());
  Assert(q.getKind() == FORALL);
  // If the conjecture is forall x1...xn. ~(x1 = t1 ^ ... xn = tn), it is
  // trivially solvable.
  std::vector<Node> args(q[0].begin(), q[0].end());
  // keep solving for variables until a fixed point is reached
  std::vector<Node> vars;
  std::vector<Node> subs;
  Node body = q[1];
  Node prev;
  while (prev != body && !args.empty())
  {
    prev = body;

    std::vector<Node> varsTmp;
    std::vector<Node> subsTmp;
    QuantifiersRewriter::getVarElim(body, false, args, varsTmp, subsTmp);
    // if we eliminated a variable, update body and reprocess
    if (!varsTmp.empty())
    {
      Assert(varsTmp.size() == subsTmp.size());
      // remake with eliminated nodes
      body = body.substitute(
          varsTmp.begin(), varsTmp.end(), subsTmp.begin(), subsTmp.end());
      body = Rewriter::rewrite(body);
      // apply to subs
      // this ensures we behave correctly if we solve x before y in
      // x = y+1 ^ y = 2.
      for (size_t i = 0, ssize = subs.size(); i < ssize; i++)
      {
        subs[i] = subs[i].substitute(
            varsTmp.begin(), varsTmp.end(), subsTmp.begin(), subsTmp.end());
        subs[i] = Rewriter::rewrite(subs[i]);
      }
      vars.insert(vars.end(), varsTmp.begin(), varsTmp.end());
      subs.insert(subs.end(), subsTmp.begin(), subsTmp.end());
    }
  }
  // if we solved all arguments
  if (args.empty() && body.isConst() && !body.getConst<bool>())
  {
    Trace("sygus-si-trivial-solve")
        << q << " is trivially solvable by substitution " << vars << " -> "
        << subs << std::endl;
    std::map<Node, Node> imap;
    for (size_t j = 0, vsize = vars.size(); j < vsize; j++)
    {
      imap[vars[j]] = subs[j];
    }
    std::vector<Node> inst;
    for (const Node& v : q[0])
    {
      Assert(imap.find(v) != imap.end());
      inst.push_back(imap[v]);
    }
    d_inst.push_back(inst);
    d_instConds.push_back(NodeManager::currentNM()->mkConst(true));
    d_isSolved = true;
    return true;
  }
  Trace("sygus-si-trivial-solve")
      << q << " is not trivially solvable." << std::endl;
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
