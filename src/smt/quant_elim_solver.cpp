/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for quantifier elimination queries.
 */

#include "smt/quant_elim_solver.h"

#include "base/modal_exception.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "expr/subtype_elim_node_converter.h"
#include "smt/smt_driver.h"
#include "smt/smt_solver.h"
#include "theory/quantifiers/cegqi/nested_qe.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "util/string.h"

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

QuantElimSolver::QuantElimSolver(Env& env, SmtSolver& sms, ContextManager* ctx)
    : EnvObj(env), d_smtSolver(sms), d_ctx(ctx)
{
}

QuantElimSolver::~QuantElimSolver() {}

Node QuantElimSolver::getQuantifierElimination(Node q,
                                               bool doFull,
                                               bool isInternalSubsolver)
{
  Trace("smt-qe") << "QuantElimSolver: get qe : " << q << std::endl;
  if (q.getKind() != Kind::EXISTS && q.getKind() != Kind::FORALL)
  {
    throw ModalException(
        "Expecting a quantified formula as argument to get-qe.");
  }
  NodeManager* nm = nodeManager();
  // ensure the body is rewritten
  q = nm->mkNode(q.getKind(), q[0], rewrite(q[1]));
  // do nested quantifier elimination if necessary
  q = quantifiers::NestedQe::doNestedQe(d_env, q, true);
  Trace("smt-qe") << "QuantElimSolver: after nested quantifier elimination : "
                  << q << std::endl;
  Node keyword =
      nm->mkConst(String(doFull ? "quant-elim" : "quant-elim-partial"));
  Node n_attr = nm->mkNode(Kind::INST_ATTRIBUTE, keyword);
  // Polarity is the Boolean constant we return if the subquery is "sat".
  bool polarity = (q.getKind() != Kind::EXISTS);
  Node ne;
  // Special case: if we have no free symbols, just use a quantifier-free
  // query. This ensures we don't depend on quantifier instantiation in
  // these cases, which is especially important if the theory does not admit
  // QE, e.g. strings.
  std::unordered_set<Node> syms;
  expr::getSymbols(q, syms);
  bool closed = false;
  if (syms.empty())
  {
    // Partial elimination is irrelevant since we have a closed formula, so we
    // assume we are doing full elimination.
    doFull = true;
    closed = true;
    Subs sq;
    SkolemManager* sm = nm->getSkolemManager();
    for (const Node& v : q[0])
    {
      Node k = sm->mkInternalSkolemFunction(
          InternalSkolemId::QE_CLOSED_INPUT, v.getType(), {v});
      sq.add(v, k);
    }
    ne = sq.apply(q[1]);
    // We are skolemizing, so we flip the polarity
    polarity = !polarity;
    if (q.getKind() == Kind::EXISTS)
    {
      ne = ne.negate();
    }
  }
  else
  {
    // tag the quantified formula with the quant-elim attribute
    TypeNode t = nm->booleanType();
    n_attr = nm->mkNode(Kind::INST_PATTERN_LIST, n_attr);
    std::vector<Node> children;
    children.push_back(q[0]);
    children.push_back(q.getKind() == Kind::EXISTS ? q[1] : q[1].negate());
    children.push_back(n_attr);
    ne = nm->mkNode(Kind::EXISTS, children);
    Assert(ne.getNumChildren() == 3);
  }
  Trace("smt-qe-debug") << "Query for quantifier elimination : " << ne
                        << std::endl;
  // use a single call driver
  SmtDriverSingleCall sdsc(d_env, d_smtSolver, d_ctx);
  Result r = sdsc.checkSat(std::vector<Node>{ne.notNode()});
  Trace("smt-qe") << "Query returned " << r << std::endl;
  if (r.getStatus() != Result::UNSAT)
  {
    if (r.getStatus() != Result::SAT && doFull)
    {
      verbose(1)
          << "While performing quantifier elimination, unexpected result : "
          << r << " for query." << std::endl;
      // failed, return original
      return q;
    }
    // must use original quantified formula to compute QE, which ensures that
    // e.g. term formula removal is not run on the body. Notice that we assume
    // that the (single) quantified formula is preprocessed, rewritten
    // version of the input quantified formula q.
    std::vector<Node> inst_qs;
    Node topq;
    Node ret;
    if (!closed)
    {
      TheoryEngine* te = d_smtSolver.getTheoryEngine();
      Assert(te != nullptr);
      QuantifiersEngine* qe = te->getQuantifiersEngine();
      qe->getInstantiatedQuantifiedFormulas(inst_qs);
      // Find the quantified formula corresponding to the quantifier elimination
      for (const Node& qinst : inst_qs)
      {
        // Should have the same attribute mark as above
        if (qinst.getNumChildren() == 3 && qinst[2] == n_attr)
        {
          topq = qinst;
          break;
        }
      }
      if (!topq.isNull())
      {
        Assert(topq.getKind() == Kind::FORALL);
        Trace("smt-qe") << "Get qe based on preprocessed quantified formula "
                        << topq << std::endl;
        std::vector<Node> insts;
        qe->getInstantiations(topq, insts);
        // note we do not convert to witness form here, since we could be
        // an internal subsolver (SolverEngine::isInternalSubsolver).
        ret = nm->mkAnd(insts);
        Trace("smt-qe") << "QuantElimSolver returned : " << ret << std::endl;
        if (q.getKind() == Kind::EXISTS)
        {
          ret = rewrite(ret.negate());
        }
        // do extended rewrite to minimize the size of the formula aggressively
        ret = extendedRewrite(ret);
        // if we are not an internal subsolver, convert to witness form, since
        // internally generated skolems should not escape
        if (!isInternalSubsolver)
        {
          ret = SkolemManager::getOriginalForm(ret);
        }
        // make so that the returned formula does not involve arithmetic
        // subtyping
        SubtypeElimNodeConverter senc(nodeManager());
        ret = senc.convert(ret);
      }
    }
    // If we are closed, or the quantified formula was not instantiated in the
    // subsolver, then we are a constant.
    if (ret.isNull())
    {
      ret = nm->mkConst(polarity);
    }
    return ret;
  }
  // otherwise, just true/false
  return nm->mkConst(!polarity);
}

}  // namespace smt
}  // namespace cvc5::internal
