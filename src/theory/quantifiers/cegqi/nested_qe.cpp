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
#include "theory/smt_engine_subsolver.h"
#include "expr/subs.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool NestedQe::registerQuantifiedFormula(Node q)
{ 
  // TODO dynamic module?
  return false;
}

bool NestedQe::getNestedQuantification(Node q, std::vector<Node>& nqs)
{
  expr::getKindSubterms(q[1], kind::FORALL, true, nqs);
  return !nqs.empty();
}

Node NestedQe::doNestedQe(Node q, bool keepTopLevel)
{
  Assert (q.getKind()==FORALL);
  std::vector<Node> nqs;
  if( !getNestedQuantification(q, nqs))
  {
    if (!keepTopLevel)
    {
      // just do ordinary quantifier elimination
      return doQe(q);
    }
    return q;
  }
  // otherwise, skolemize the arguments of this and apply
  std::vector<Node> vars(q[0].begin(), q[0].end());
  Subs sk;
  sk.add(vars);
  Subs snqe;
  for (const Node& nq : nqs)
  {
    Node nqk = sk.apply(nq);
    Node nqqe = doNestedQe(q);
    snqe.add(nqk, nqqe);
  }
  Node qeBody = sk.apply(q[1]);
  qeBody = snqe.apply(qeBody);
  qeBody = sk.rapply(qeBody, true);
  std::vector<Node> qargs;
  qargs.push_back(q[0]);
  qargs.push_back(qeBody);
  if (q.getNumChildren()==3)
  {
    qargs.push_back(q[2]);
  }
  return nm->mkNode(FORALL, qargs);
}

Node NestedQe::doQe(Node q)
{
  Assert (q.getKind()==FORALL);
  NodeManager * nm = NodeManager::currentNM();
  q = nm->mkNode(EXISTS, q[0], q[1].negate());
  std::unique_ptr<SmtEngine> smt_qe;
  initializeSubsolver(smt_qe);
  return smt_qe->getQuantifierElimination(q, true, false);
}

}
}
}

