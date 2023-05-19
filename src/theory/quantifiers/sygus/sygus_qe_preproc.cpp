/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus quantifier elimination preprocessor.
 */

#include "theory/quantifiers/sygus/sygus_qe_preproc.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusQePreproc::SygusQePreproc(Env& env) : EnvObj(env) {}

Node SygusQePreproc::preprocess(Node q)
{
  Node body = q[1];
  if (body.getKind() == NOT && body[0].getKind() == FORALL)
  {
    body = body[0][1];
  }
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Trace("cegqi-qep") << "Compute single invocation for " << q << "..."
                     << std::endl;
  quantifiers::SingleInvocationPartition sip(d_env);
  std::vector<Node> funcs0;
  funcs0.insert(funcs0.end(), q[0].begin(), q[0].end());
  sip.init(funcs0, body);
  Trace("cegqi-qep") << "...finished, got:" << std::endl;
  sip.debugPrint("cegqi-qep");

  if (sip.isPurelySingleInvocation() || !sip.isNonGroundSingleInvocation())
  {
    return Node::null();
  }
  // create new smt engine to do quantifier elimination
  std::unique_ptr<SolverEngine> smt_qe;
  initializeSubsolver(smt_qe, d_env);
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
    if (std::find(funcs0.begin(), funcs0.end(), v) != funcs0.end())
    {
      Trace("cegqi-qep") << "- fun var: " << v << std::endl;
    }
    else if (std::find(si_vars.begin(), si_vars.end(), v) == si_vars.end())
    {
      qe_vars.push_back(v);
      Trace("cegqi-qep") << "- qe var: " << v << std::endl;
    }
    else
    {
      nqe_vars.push_back(v);
      Trace("cegqi-qep") << "- non qe var: " << v << std::endl;
    }
  }
  std::vector<Node> orig;
  std::vector<Node> subs;
  // skolemize non-qe variables
  for (unsigned i = 0, size = nqe_vars.size(); i < size; i++)
  {
    Node k = sm->mkDummySkolem(
        "k", nqe_vars[i].getType(), "qe for non-ground single invocation");
    orig.push_back(nqe_vars[i]);
    subs.push_back(k);
    Trace("cegqi-qep") << "  subs : " << nqe_vars[i] << " -> " << k
                       << std::endl;
  }
  std::vector<Node> funcs1;
  sip.getFunctions(funcs1);
  for (unsigned i = 0, size = funcs1.size(); i < size; i++)
  {
    Node f = funcs1[i];
    Node fi = sip.getFunctionInvocationFor(f);
    Node fv = sip.getFirstOrderVariableForFunction(f);
    Assert(!fi.isNull());
    orig.push_back(fi);
    Node k = sm->mkDummySkolem(
        "k", fv.getType(), "qe for function in non-ground single invocation");
    subs.push_back(k);
    Trace("cegqi-qep") << "  subs : " << fi << " -> " << k << std::endl;
  }
  Node conj_se_ngsi = sip.getFullSpecification();
  Trace("cegqi-qep") << "Full specification is " << conj_se_ngsi << std::endl;
  Node conj_se_ngsi_subs = conj_se_ngsi.substitute(
      orig.begin(), orig.end(), subs.begin(), subs.end());
  Assert(!qe_vars.empty());
  conj_se_ngsi_subs = nm->mkNode(
      EXISTS, nm->mkNode(BOUND_VAR_LIST, qe_vars), conj_se_ngsi_subs.negate());

  Trace("cegqi-qep") << "Run quantifier elimination on " << conj_se_ngsi_subs
                     << std::endl;
  Node qeRes = smt_qe->getQuantifierElimination(conj_se_ngsi_subs, true);
  Trace("cegqi-qep") << "Result : " << qeRes << std::endl;

  // create single invocation conjecture, if QE was successful
  if (!expr::hasBoundVar(qeRes))
  {
    qeRes =
        qeRes.substitute(subs.begin(), subs.end(), orig.begin(), orig.end());
    if (!nqe_vars.empty())
    {
      qeRes = nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, nqe_vars), qeRes);
    }
    Assert(q.getNumChildren() == 3);
    qeRes = nm->mkNode(FORALL, q[0], qeRes, q[2]);
    Trace("cegqi-qep") << "Converted conjecture after QE : " << qeRes
                       << std::endl;
    qeRes = rewrite(qeRes);
    // it is equivalent to the original
    Trace("cegqi-lemma") << "Cegqi::Lemma : qe-preprocess : " << qeRes
                         << std::endl;
    return qeRes;
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
