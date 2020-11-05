/*********************                                                        */
/*! \file nested_qe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Methods for counterexample-guided quantifier instantiation
 ** based on nested quantifier elimination.
 **/

#include "theory/quantifiers/cegqi/nested_qe.h"

#include "expr/node_algorithm.h"
#include "expr/subs.h"
#include "theory/smt_engine_subsolver.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

NestedQe::NestedQe(context::UserContext* u) : d_qnqe(u) {}

bool NestedQe::process(Node q, std::vector<Node>& lems)
{
  NodeNodeMap::iterator it = d_qnqe.find(q);
  if (it != d_qnqe.end())
  {
    // already processed
    return (*it).second != q;
  }
  Trace("cegqi-nested-qe") << "Do nested QE on " << q << std::endl;
  Node qqe = doNestedQe(q, true);
  d_qnqe[q] = qqe;
  if (qqe == q)
  {
    Trace("cegqi-nested-qe")
        << "Did not apply nested QE to " << qqe << std::endl;
    return false;
  }
  Trace("cegqi-nested-qe") << "Applied nested QE to " << q << std::endl;
  Trace("cegqi-nested-qe") << "Result is " << qqe << std::endl;

  // add as lemma
  lems.push_back(q.eqNode(qqe));
  return true;
}

bool NestedQe::getNestedQuantification(
    Node q, std::unordered_set<Node, NodeHashFunction>& nqs)
{
  expr::getKindSubterms(q[1], kind::FORALL, true, nqs);
  return !nqs.empty();
}

Node NestedQe::doNestedQe(Node q, bool keepTopLevel)
{
  Assert(q.getKind() == kind::FORALL);
  std::unordered_set<Node, NodeHashFunction> nqs;
  if (!getNestedQuantification(q, nqs))
  {
    Trace("cegqi-nested-qe-debug")
        << "...no nested quantification" << std::endl;
    if (keepTopLevel)
    {
      return q;
    }
    // just do ordinary quantifier elimination
    Node qqe = doQe(q);
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
    Node nqqe = doNestedQe(nqk);
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
  qeBody = sk.rapply(qeBody, true);
  // reconstruct the body
  std::vector<Node> qargs;
  qargs.push_back(q[0]);
  qargs.push_back(qeBody);
  if (q.getNumChildren() == 3)
  {
    qargs.push_back(q[2]);
  }
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(kind::FORALL, qargs);
}

Node NestedQe::doQe(Node q)
{
  Assert(q.getKind() == kind::FORALL);
  Trace("cegqi-nested-qe-debug") << "Apply qe to " << q << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  q = nm->mkNode(kind::EXISTS, q[0], q[1].negate());
  std::unique_ptr<SmtEngine> smt_qe;
  initializeSubsolver(smt_qe);
  Node qqe = smt_qe->getQuantifierElimination(q, true, false);
  if (expr::hasBoundVar(qqe))
  {
    //...failed to apply
    return q;
  }
  return qqe.negate();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
