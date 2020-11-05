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

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool NestedQe::registerQuantifiedFormula(Node q)
{ 
  // TODO ?
  return false;
}

bool NestedQe::getNestedQuantification(Node q, std::vector<Node>& nqs)
{
  
}

Node NestedQe::doNestedQe(Node q)
{
  
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

