/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for processing single invocation synthesis conjectures.
 */
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_reconstruct.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

CegSingleInv::CegSingleInv(Env& env, TermRegistry& tr, SygusStatistics& s)
    : EnvObj(env),
      d_isSolved(false),
      d_sip(new SingleInvocationPartition(env)),
      d_srcons(new SygusReconstruct(env, tr.getTermDatabaseSygus(), s)),
      d_single_invocation(false),
      d_treg(tr)
{
}

CegSingleInv::~CegSingleInv()
{
  delete d_sip;  // d_sip(new SingleInvocationPartition),
}

void CegSingleInv::initialize(Node q)
{
  // can only register one quantified formula with this
  Assert(d_quant.isNull());
  d_quant = q;
  d_simp_quant = q;
  Trace("sygus-si") << "CegSingleInv::initialize : " << q << std::endl;

  // decompose the conjecture
  SygusUtils::decomposeSygusConjecture(d_quant, d_funs, d_unsolvedf, d_solvedf);

  Trace("sygus-si") << "functions: " << d_funs << std::endl;
  Trace("sygus-si") << " unsolved: " << d_unsolvedf << std::endl;
  Trace("sygus-si") << "   solved: " << d_solvedf << std::endl;

  // infer single invocation-ness

  // get the variables
  std::map<Node, std::vector<Node> > progVars;
  for (const Node& sf : q[0])
  {
    // get its argument list
    SygusUtils::getOrMkSygusArgumentList(sf, progVars[sf]);
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
  if (!d_sip->init(d_unsolvedf, qq))
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
    Assert(std::find(d_funs.begin(), d_funs.end(), funcs[j]) != d_funs.end());
    d_prog_to_sol_index[funcs[j]] = j;
  }

  // check if it is single invocation
  if (d_sip->isPurelySingleInvocation())
  {
    // We are fully single invocation, set single invocation if we haven't
    // disabled single invocation techniques.
    if (options().quantifiers.cegqiSingleInvMode
        != options::CegqiSingleInvMode::NONE)
    {
      d_single_invocation = true;
    }
  }
}

void CegSingleInv::finishInit(bool syntaxRestricted)
{
  Trace("sygus-si-debug") << "Single invocation: finish init" << std::endl;
  // do not do single invocation if grammar is restricted and
  // options::CegqiSingleInvMode::ALL is not enabled
  if (options().quantifiers.cegqiSingleInvMode
          == options::CegqiSingleInvMode::USE
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
    if (options().quantifiers.cegqiSingleInvAbort)
    {
      std::stringstream ss;
      ss << "Property is not handled by single invocation." << std::endl;
      throw LogicException(ss.str());
    }
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
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
    Node v =
        sm->mkDummySkolem("a", sivars[i].getType(), "single invocation arg");
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
    // if the conjecture is trivially solvable, set the solution
    if (solveTrivial(d_single_inv))
    {
      setSolution();
    }
    else
    {
      status = CegInstantiator::isCbqiQuant(d_single_inv,
                                            options().quantifiers.cegqiAll);
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

Result CegSingleInv::solve()
{
  if (d_single_inv.isNull())
  {
    // not using single invocation techniques
    return Result(Result::UNKNOWN);
  }
  if (d_isSolved)
  {
    // already solved, probably via a call to solveTrivial.
    return Result(Result::UNSAT);
  }
  Trace("sygus-si") << "Solve using single invocation..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // Mark the quantified formula with the quantifier elimination attribute to
  // ensure its structure is preserved in the query below.
  Node siq = d_single_inv;
  Node n_attr;
  if (siq.getKind() == FORALL)
  {
    n_attr = sm->mkDummySkolem(
        "qe_si",
        nm->booleanType(),
        "Auxiliary variable for qe attr for single invocation.");
    QuantElimAttribute qea;
    n_attr.setAttribute(qea, true);
    n_attr = nm->mkNode(INST_ATTRIBUTE, n_attr);
    n_attr = nm->mkNode(INST_PATTERN_LIST, n_attr);
    siq = nm->mkNode(FORALL, siq[0], siq[1], n_attr);
  }
  // solve the single invocation conjecture using a fresh copy of SMT engine
  std::unique_ptr<SolverEngine> siSmt;
  initializeSubsolver(siSmt, d_env);
  // do not use shared selectors in subsolver, since this leads to solutions
  // with non-user symbols
  siSmt->setOption("dt-share-sel", "false");
  siSmt->assertFormula(siq);
  Result r = siSmt->checkSat();
  Trace("sygus-si") << "Result: " << r << std::endl;
  Result::Status res = r.getStatus();
  if (res != Result::UNSAT)
  {
    if (res != Result::SAT)
    {
      warning()
          << "Warning : the single invocation solver determined the SyGuS "
             "conjecture may be infeasible"
          << std::endl;
    }
    // conjecture is infeasible or unknown
    return r;
  }
  // now, get the instantiations
  std::vector<Node> qs;
  siSmt->getInstantiatedQuantifiedFormulas(qs);
  // track the instantiations, as solution construction is based on this
  Trace("sygus-si") << "#instantiated quantified formulas=" << qs.size()
                    << std::endl;
  d_inst.clear();
  d_instConds.clear();
  Node q;
  // look for the quantified formula with the appropriate attribute that we
  // marked above.
  for (const Node& qss : qs)
  {
    if (qss.getNumChildren() == 3 && qss[2] == n_attr)
    {
      q = qss;
      break;
    }
  }
  // if the quantified formula was instantiated in the query
  if (!q.isNull())
  {
    Assert(q.getKind() == FORALL);
    siSmt->getInstantiationTermVectors(q, d_inst);
    Trace("sygus-si") << "#instantiations of " << q << "=" << d_inst.size()
                      << std::endl;
    // We use the original synthesis conjecture siq, since q may contain
    // internal symbols e.g. termITE skolem after preprocessing.
    std::vector<Node> vars;
    for (const Node& v : siq[0])
    {
      vars.push_back(v);
    }
    Node body = siq[1];
    for (unsigned i = 0, ninsts = d_inst.size(); i < ninsts; i++)
    {
      // note we do not convert to witness form here, since we could be
      // an internal subsolver
      std::vector<Node>& inst = d_inst[i];
      Trace("sygus-si") << "  Instantiation: " << inst << std::endl;
      // instantiation should have same arity since we are not allowed to
      // eliminate variables from quantifiers marked with QuantElimAttribute.
      Assert(inst.size() == vars.size());
      Node ilem =
          body.substitute(vars.begin(), vars.end(), inst.begin(), inst.end());
      ilem = rewrite(ilem);
      d_instConds.push_back(ilem);
      Trace("sygus-si") << "  Instantiation Lemma: " << ilem << std::endl;
    }
  }
  // set the solution
  setSolution();
  return res;
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

Node CegSingleInv::getSolution(size_t sol_index,
                               TypeNode stn,
                               int8_t& reconstructed,
                               bool rconsSygus)
{
  Assert(sol_index < d_quant[0].getNumChildren());
  Node f = d_quant[0][sol_index];
  Trace("csi-sol") << "CegSingleInv::getSolution " << f << std::endl;
  // maybe it is in the solved map already?
  if (d_solvedf.contains(f))
  {
    // notice that we ignore d_solutions for solved functions
    Trace("csi-sol") << "...return solution from annotation" << std::endl;
    return d_solvedf.apply(f);
  }
  Trace("csi-sol") << "...get solution from vector" << std::endl;

  Node s = d_solutions[sol_index];
  Node sol = s.getKind() == LAMBDA ? s[1] : s;
  // must substitute to be proper variables
  const DType& dt = stn.getDType();
  Node varList = dt.getSygusVarList();
  Assert(d_single_inv_arg_sk.size() == varList.getNumChildren());
  std::vector<Node> vars;
  std::vector<Node> sygusVars;
  for (size_t i = 0, nvars = d_single_inv_arg_sk.size(); i < nvars; i++)
  {
    Trace("csi-sol") << d_single_inv_arg_sk[i] << " ";
    vars.push_back(d_single_inv_arg_sk[i]);
    sygusVars.push_back(varList[i]);
  }
  Trace("csi-sol") << std::endl;
  sol = sol.substitute(
      vars.begin(), vars.end(), sygusVars.begin(), sygusVars.end());
  sol = reconstructToSyntax(sol, stn, reconstructed, rconsSygus);
  return !sol.isNull() && s.getKind() == LAMBDA
             ? NodeManager::currentNM()->mkNode(LAMBDA, s[0], sol)
             : sol;
}

Node CegSingleInv::getSolutionFromInst(size_t index)
{
  Node prog = d_quant[0][index];
  Node s;
  // If it is unconstrained: either the variable does not appear in the
  // conjecture or the conjecture can be solved without a single instantiation.
  if (d_prog_to_sol_index.find(prog) == d_prog_to_sol_index.end()
      || d_inst.empty())
  {
    TypeNode ptn = prog.getType();
    if (ptn.isFunction())
    {
      ptn = ptn.getRangeType();
    }
    Trace("csi-sol") << "Get solution for (unconstrained) " << prog << std::endl;
    s = d_treg.getTermEnumeration()->getEnumerateTerm(ptn, 0);
  }
  else
  {
    Trace("csi-sol") << "Get solution for " << prog << ", with skolems : ";
    size_t sol_index = d_prog_to_sol_index[prog];

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
  }
  //simplify the solution using the extended rewriter
  Trace("csi-sol") << "Solution (pre-simplification): " << s << std::endl;
  s = extendedRewrite(s);
  Trace("csi-sol") << "Solution (post-simplification): " << s << std::endl;
  // wrap into lambda, as needed
  return SygusUtils::wrapSolution(prog, s);
}

void CegSingleInv::setSolution()
{
  // construct the solutions based on the instantiations
  d_solutions.clear();
  d_rcSolutions.clear();
  Subs finalSol;
  for (size_t i = 0, nvars = d_quant[0].getNumChildren(); i < nvars; i++)
  {
    // Note this is a dummy solution for solved functions, which are given
    // solutions in the annotation but do not appear in the conjecture.
    Node sol = getSolutionFromInst(i);
    d_solutions.push_back(sol);
    // haven't reconstructed to syntax yet
    d_rcSolutions.push_back(Node::null());
    finalSol.add(d_quant[0][i], sol);
  }
  d_isSolved = true;
  if (!d_solvedf.empty())
  {
    // replace the final solution into the solved functions
    finalSol.applyToRange(d_solvedf);
    // rewrite the solution
    for (Node& n : d_solvedf.d_subs)
    {
      n = rewrite(n);
    }
  }
}

Node CegSingleInv::reconstructToSyntax(Node s,
                                       TypeNode stn,
                                       int8_t& reconstructed,
                                       bool rconsSygus)
{
  // extract the lambda body
  Node sol = s;
  const DType& dt = stn.getDType();

  // reconstruct the solution into sygus if necessary
  reconstructed = 0;
  if (options().quantifiers.cegqiSingleInvReconstruct
          != options::CegqiSingleInvRconsMode::NONE
      && !dt.getSygusAllowAll() && !stn.isNull() && rconsSygus)
  {
    int64_t enumLimit = -1;
    if (options().quantifiers.cegqiSingleInvReconstruct
        == options::CegqiSingleInvRconsMode::TRY)
    {
      enumLimit = 0;
    }
    else if (options().quantifiers.cegqiSingleInvReconstruct
             == options::CegqiSingleInvRconsMode::ALL_LIMIT)
    {
      enumLimit = options().quantifiers.cegqiSingleInvReconstructLimit;
    }
    sol = d_srcons->reconstructSolution(s, stn, reconstructed, enumLimit);
    if (reconstructed == 1)
    {
      Trace("csi-sol") << "Solution (post-reconstruction into Sygus): " << sol
                       << std::endl;
    }
  }
  else
  {
    Trace("csi-sol") << "Post-process solution..." << std::endl;
    Node prev = sol;
    sol = extendedRewrite(sol);
    if (prev != sol)
    {
      Trace("csi-sol") << "Solution (after post process) : " << sol
                       << std::endl;
    }
  }

  if (reconstructed == -1)
  {
    return Node::null();
  }
  return sol;
}

void CegSingleInv::ppNotifyConjecture(Node q) { d_orig_conjecture = q; }

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
    QuantifiersRewriter qrew(d_env.getRewriter(), options());
    qrew.getVarElim(body, args, varsTmp, subsTmp);
    // if we eliminated a variable, update body and reprocess
    if (!varsTmp.empty())
    {
      Assert(varsTmp.size() == subsTmp.size());
      // remake with eliminated nodes
      body = body.substitute(
          varsTmp.begin(), varsTmp.end(), subsTmp.begin(), subsTmp.end());
      body = rewrite(body);
      // apply to subs
      // this ensures we behave correctly if we solve x before y in
      // x = y+1 ^ y = 2.
      for (size_t i = 0, ssize = subs.size(); i < ssize; i++)
      {
        subs[i] = subs[i].substitute(
            varsTmp.begin(), varsTmp.end(), subsTmp.begin(), subsTmp.end());
        subs[i] = rewrite(subs[i]);
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
    return true;
  }
  Trace("sygus-si-trivial-solve")
      << q << " is not trivially solvable." << std::endl;

  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
