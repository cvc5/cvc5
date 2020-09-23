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

namespace CVC4 {
namespace theory {
namespace bags {

bool NormalForm::checkNormalConstant(TNode n)
{
  // TODO(projects#223): complete this function
  return false;
}

Node NormalForm::getNormalForm(TNode n)
{
  Assert(AreChildrenInNormalForm(n))
      << "Expected the children of '" << n << "' to be constants" << std::endl;
  Kind k = n.getKind();
  NodeManager* nm = NodeManager::currentNM();
  switch (k)
  {
    case kind::MK_BAG:
    {
      // zero or negative multiplicity
      Assert(n[1].getConst<Rational>().sgn() != 1);
      // return an empty bag
      Node emptybag = nm->mkConst(EmptyBag(n[0].getType()));
      return emptybag;
    }
  }
  return n;
}

bool NormalForm::AreChildrenInNormalForm(TNode n)
{
  return std::all_of(
      n.begin(), n.end(), [](TNode child) { return child.isConst(); });
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4