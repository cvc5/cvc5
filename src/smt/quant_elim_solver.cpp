/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for quantifier elimination queries.
 */

#include "smt/quant_elim_solver.h"

#include "base/modal_exception.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "smt/smt_solver.h"
#include "theory/quantifiers/cegqi/nested_qe.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/string.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace smt {

QuantElimSolver::QuantElimSolver(Env& env, SmtSolver& sms)
    : d_env(env), d_smtSolver(sms)
{
}

QuantElimSolver::~QuantElimSolver() {}

Node QuantElimSolver::getQuantifierElimination(Assertions& as,
                                               Node q,
                                               bool doFull,
                                               bool isInternalSubsolver)
{
  Trace("smt-qe") << "QuantElimSolver: get qe : " << q << std::endl;
  if (q.getKind() != EXISTS && q.getKind() != FORALL)
  {
    throw ModalException(
        "Expecting a quantified formula as argument to get-qe.");
  }
  NodeManager* nm = NodeManager::currentNM();
  // ensure the body is rewritten
  q = nm->mkNode(q.getKind(), q[0], Rewriter::rewrite(q[1]));
  // do nested quantifier elimination if necessary
  q = quantifiers::NestedQe::doNestedQe(d_env, q, true);
  Trace("smt-qe") << "QuantElimSolver: after nested quantifier elimination : "
                  << q << std::endl;
  // tag the quantified formula with the quant-elim attribute
  TypeNode t = nm->booleanType();
  TheoryEngine* te = d_smtSolver.getTheoryEngine();
  Assert(te != nullptr);
  Node keyword =
      nm->mkConst(String(doFull ? "quant-elim" : "quant-elim-partial"));
  Node n_attr = nm->mkNode(INST_ATTRIBUTE, keyword);
  n_attr = nm->mkNode(INST_PATTERN_LIST, n_attr);
  std::vector<Node> children;
  children.push_back(q[0]);
  children.push_back(q.getKind() == EXISTS ? q[1] : q[1].negate());
  children.push_back(n_attr);
  Node ne = nm->mkNode(EXISTS, children);
  Trace("smt-qe-debug") << "Query for quantifier elimination : " << ne
                        << std::endl;
  Assert(ne.getNumChildren() == 3);
  // We consider this to be an entailment check, which also avoids incorrect
  // status reporting (see SmtEngineState::d_expectedStatus).
  Result r = d_smtSolver.checkSatisfiability(as, std::vector<Node>{ne}, true);
  Trace("smt-qe") << "Query returned " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
  {
    if (r.asSatisfiabilityResult().isSat() != Result::SAT && doFull)
    {
      Notice()
          << "While performing quantifier elimination, unexpected result : "
          << r << " for query.";
      // failed, return original
      return q;
    }
    QuantifiersEngine* qe = te->getQuantifiersEngine();
    // must use original quantified formula to compute QE, which ensures that
    // e.g. term formula removal is not run on the body. Notice that we assume
    // that the (single) quantified formula is preprocessed, rewritten
    // version of the input quantified formula q.
    std::vector<Node> inst_qs;
    qe->getInstantiatedQuantifiedFormulas(inst_qs);
    Assert(inst_qs.size() <= 1);
    Node ret;
    if (inst_qs.size() == 1)
    {
      Node topq = inst_qs[0];
      Assert(topq.getKind() == FORALL);
      Trace("smt-qe") << "Get qe based on preprocessed quantified formula "
                      << topq << std::endl;
      std::vector<Node> insts;
      qe->getInstantiations(topq, insts);
      // note we do not convert to witness form here, since we could be
      // an internal subsolver (SmtEngine::isInternalSubsolver).
      ret = nm->mkAnd(insts);
      Trace("smt-qe") << "QuantElimSolver returned : " << ret << std::endl;
      if (q.getKind() == EXISTS)
      {
        ret = Rewriter::rewrite(ret.negate());
      }
    }
    else
    {
      ret = nm->mkConst(q.getKind() != EXISTS);
    }
    // do extended rewrite to minimize the size of the formula aggressively
    theory::quantifiers::ExtendedRewriter extr(true);
    ret = extr.extendedRewrite(ret);
    // if we are not an internal subsolver, convert to witness form, since
    // internally generated skolems should not escape
    if (!isInternalSubsolver)
    {
      ret = SkolemManager::getOriginalForm(ret);
    }
    return ret;
  }
  // otherwise, just true/false
  return nm->mkConst(q.getKind() == EXISTS);
}

}  // namespace smt
}  // namespace cvc5
