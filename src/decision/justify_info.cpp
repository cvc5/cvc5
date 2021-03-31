/*********************                                                        */
/*! \file justify_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification info
 **/

#include "decision/justify_info.h"

namespace CVC5 {

JustifyInfo::JustifyInfo(context::Context* c)
    : d_node(c), d_desiredVal(c, prop::SAT_VALUE_UNKNOWN), d_childIndex(c, 0)
{
}

JustifyInfo::~JustifyInfo() {}

JustifyNode JustifyInfo::getNode() const
{
  return JustifyNode(d_node.get(), d_desiredVal.get());
}

size_t JustifyInfo::getNextChildIndex()
{
  size_t i = d_childIndex.get();
  d_childIndex = d_childIndex + 1;
  return i;
}
void JustifyInfo::revertChildIndex()
{
  Assert(d_childIndex.get() > 0);
  d_childIndex = d_childIndex - 1;
}
void JustifyInfo::set(TNode n, prop::SatValue desiredVal)
{
  d_node = n;
  d_desiredVal = desiredVal;
  d_childIndex = 0;
}

}  // namespace CVC5
