/*********************                                                        */
/*! \file quant_elim_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for quantifier elimination queries
 **/

#include "smt/quant_elim_solver.h"

#include "smt/smt_solver.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

QuantElimSolver::QuantElimSolver(SmtSolver& sms) : d_smtSolver(sms) {}

QuantElimSolver::~QuantElimSolver() {}

Node QuantElimSolver::getQuantifierElimination(Assertions& as,
                                               Node e,
                                               bool doFull)
{
  Trace("smt-qe") << "Do quantifier elimination " << e << std::endl;
  if (e.getKind() != EXISTS && e.getKind() != FORALL)
  {
    throw ModalException(
        "Expecting a quantified formula as argument to get-qe.");
  }
  NodeManager* nm = NodeManager::currentNM();
  // tag the quantified formula with the quant-elim attribute
  TypeNode t = nm->booleanType();
  Node n_attr = nm->mkSkolem("qe", t, "Auxiliary variable for qe attr.");
  std::vector<Node> node_values;
  TheoryEngine* te = d_smtSolver.getTheoryEngine();
  Assert(te != nullptr);
  te->setUserAttribute(
      doFull ? "quant-elim" : "quant-elim-partial", n_attr, node_values, "");
  n_attr = nm->mkNode(INST_ATTRIBUTE, n_attr);
  n_attr = nm->mkNode(INST_PATTERN_LIST, n_attr);
  std::vector<Node> children;
  children.push_back(e[0]);
  children.push_back(e.getKind() == EXISTS ? e[1] : e[1].negate());
  children.push_back(n_attr);
  Node ne = nm->mkNode(EXISTS, children);
  Trace("smt-qe-debug") << "Query for quantifier elimination : " << ne
                        << std::endl;
  Assert(ne.getNumChildren() == 3);
  Result r =
      d_smtSolver.checkSatisfiability(as, std::vector<Node>{ne}, false, true);
  Trace("smt-qe") << "Query returned " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
  {
    if (r.asSatisfiabilityResult().isSat() != Result::SAT && doFull)
    {
      Notice()
          << "While performing quantifier elimination, unexpected result : "
          << r << " for query.";
      // failed, return original
      return e;
    }
    std::vector<Node> inst_qs;
    te->getInstantiatedQuantifiedFormulas(inst_qs);
    Assert(inst_qs.size() <= 1);
    Node ret;
    if (inst_qs.size() == 1)
    {
      Node top_q = inst_qs[0];
      Assert(top_q.getKind() == FORALL);
      Trace("smt-qe") << "Get qe for " << top_q << std::endl;
      ret = te->getInstantiatedConjunction(top_q);
      Trace("smt-qe") << "Returned : " << ret << std::endl;
      if (e.getKind() == EXISTS)
      {
        ret = Rewriter::rewrite(ret.negate());
      }
    }
    else
    {
      ret = nm->mkConst(e.getKind() != EXISTS);
    }
    // do extended rewrite to minimize the size of the formula aggressively
    theory::quantifiers::ExtendedRewriter extr(true);
    ret = extr.extendedRewrite(ret);
    return ret;
  }
  // otherwise, just true/false
  return nm->mkConst(e.getKind() == EXISTS);
}

}  // namespace smt
}  // namespace CVC4
