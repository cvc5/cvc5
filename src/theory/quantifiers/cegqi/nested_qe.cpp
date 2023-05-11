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
 * Methods for counterexample-guided quantifier instantiation
 * based on nested quantifier elimination.
 */

#include "theory/quantifiers/cegqi/nested_qe.h"

#include "expr/node_algorithm.h"
#include "expr/subs.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

NestedQe::NestedQe(Env& env) : d_env(env), d_qnqe(d_env.getUserContext()) {}

bool NestedQe::process(Node q, std::vector<Node>& lems)
{
  NodeNodeMap::iterator it = d_qnqe.find(q);
  if (it != d_qnqe.end())
  {
    // already processed
    return (*it).second != q;
  }
  Trace("cegqi-nested-qe") << "Check nested QE on " << q << std::endl;
  Node qqe = doNestedQe(d_env, q, true);
  d_qnqe[q] = qqe;
  if (qqe == q)
  {
    Trace("cegqi-nested-qe") << "...did not apply nested QE" << std::endl;
    return false;
  }
  Trace("cegqi-nested-qe") << "...applied nested QE" << std::endl;
  Trace("cegqi-nested-qe") << "Result is " << qqe << std::endl;

  // add as lemma
  lems.push_back(q.eqNode(qqe));
  return true;
}

bool NestedQe::hasProcessed(Node q) const
{
  return d_qnqe.find(q) != d_qnqe.end();
}

bool NestedQe::getNestedQuantification(Node q, std::unordered_set<Node>& nqs)
{
  expr::getKindSubterms(q[1], kind::FORALL, true, nqs);
  return !nqs.empty();
}

bool NestedQe::hasNestedQuantification(Node q)
{
  std::unordered_set<Node> nqs;
  return getNestedQuantification(q, nqs);
}

Node NestedQe::doNestedQe(Env& env, Node q, bool keepTopLevel)
{
  NodeManager* nm = NodeManager::currentNM();
  Node qOrig = q;
  bool inputExists = false;
  if (q.getKind() == kind::EXISTS)
  {
    q = nm->mkNode(kind::FORALL, q[0], q[1].negate());
    inputExists = true;
  }
  Assert(q.getKind() == kind::FORALL);
  std::unordered_set<Node> nqs;
  if (!getNestedQuantification(q, nqs))
  {
    Trace("cegqi-nested-qe-debug")
        << "...no nested quantification" << std::endl;
    if (keepTopLevel)
    {
      return qOrig;
    }
    // just do ordinary quantifier elimination
    Node qqe = doQe(env, q);
    Trace("cegqi-nested-qe-debug") << "...did ordinary qe" << std::endl;
    return qqe;
  }
  Trace("cegqi-nested-qe-debug")
      << "..." << nqs.size() << " nested quantifiers" << std::endl;
  // otherwise, skolemize the arguments of this and apply
  std::vector<Node> vars(q[0].begin(), q[0].end());
  Subs sk;
  sk.add(vars);
  // do nested quantifier elimination on each nested quantifier, skolemizing the
  // free variables
  Subs snqe;
  for (const Node& nq : nqs)
  {
    Node nqk = sk.apply(nq);
    Node nqqe = doNestedQe(env, nqk);
    if (nqqe == nqk)
    {
      // failed
      Trace("cegqi-nested-qe-debug")
          << "...failed to apply to nested" << std::endl;
      return q;
    }
    snqe.add(nqk, nqqe);
  }
  // get the result of nested quantifier elimination
  Node qeBody = sk.apply(q[1]);
  qeBody = snqe.apply(qeBody);
  // undo the skolemization
  qeBody = sk.rapply(qeBody);
  qeBody = env.getRewriter()->rewrite(qeBody);
  // reconstruct the body
  std::vector<Node> qargs;
  qargs.push_back(q[0]);
  qargs.push_back(inputExists ? qeBody.negate() : qeBody);
  if (q.getNumChildren() == 3)
  {
    qargs.push_back(q[2]);
  }
  return nm->mkNode(inputExists ? kind::EXISTS : kind::FORALL, qargs);
}

Node NestedQe::doQe(Env& env, Node q)
{
  Assert(q.getKind() == kind::FORALL);
  Trace("cegqi-nested-qe") << "  Apply qe to " << q << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  q = nm->mkNode(kind::EXISTS, q[0], q[1].negate());
  std::unique_ptr<SolverEngine> smt_qe;
  initializeSubsolver(smt_qe, env);
  Node qqe = smt_qe->getQuantifierElimination(q, true);
  if (expr::hasBoundVar(qqe))
  {
    Trace("cegqi-nested-qe") << "  ...failed QE" << std::endl;
    //...failed to apply
    return q;
  }
  Node res = qqe.negate();
  Trace("cegqi-nested-qe") << "  ...success, result = " << res << std::endl;
  return res;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
