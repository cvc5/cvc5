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

bool NormalForm::AreChildrenConstants(TNode n)
{
  return std::all_of(n.begin(), n.end(), [](Node c) { return c.isConst(); });
}

Node NormalForm::evaluate(TNode n)
{
  // TODO(projects#223): complete this function
  return CVC4::Node();
}
}  // namespace bags
}  // namespace theory
}  // namespace CVC4