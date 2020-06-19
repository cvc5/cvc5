/*********************                                                        */
/*! \file rewrite_db_sc.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database side condition utility
 **/

#include "theory/rewrite_db_sc.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

RdbSideConditionEvaluator::RdbSideConditionEvaluator()
{
}

bool RdbSideConditionEvaluator::isSideCondition(Node f)
{
  return false;
}

Node RdbSideConditionEvaluator::runSideCondition(Node f, const std::vector<Node>& args)
{
  return Node::null();
}
  
}  // namespace theory
}  // namespace CVC4
