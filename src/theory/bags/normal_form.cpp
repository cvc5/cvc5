/*************************                                                    */
/*! \file normal_form.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **/

#include "normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

bool NormalForm::checkNormalConstant(TNode n)
{
  // TODO(projects#223): complete this function
  return false;
}

bool NormalForm::areChildrenConstants(TNode n)
{
  return std::all_of(n.begin(), n.end(), [](Node c) { return c.isConst(); });
}

Node NormalForm::evaluate(TNode n)
{
  // TODO(projects#223): complete this function
  // the caller of this function should provide a node with constant arguments
  Assert(areChildrenConstants(n));
  if (n.isConst())
  {
    // a constant node is already in a normal form
    return n;
  }
  switch (n.getKind())
  {
    case MK_BAG: return evaluateMakeBag(n);
    default:
    {
    }
    break;
  }
  Unhandled() << "Unexpected kind '" << n.getKind() << "' in node " << n
              << std::endl;
}

Node NormalForm::evaluateMakeBag(TNode n)
{
  Assert(!n.isConst());
  // TODO: use the type operator for mkBag
  Node emptybag = NodeManager::currentNM()->mkConst(EmptyBag(n.getType()));
  return emptybag;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4