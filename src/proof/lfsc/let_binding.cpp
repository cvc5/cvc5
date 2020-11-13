/*********************                                                        */
/*! \file let_binding.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A let binding
 **/

#include "proof/lfsc/let_binding.h"

#include "proof/lfsc/letify.h"

namespace CVC4 {
namespace proof {
  
LetBinding::LetBinding() : d_context(), d_visitList(&d_context), d_count(&d_context), d_letList(&d_letList), d_letMap(&d_context){}
void LetBinding::push(Node n)
{
  d_context.push();
}

void LetBinding::pop()
{
  d_context.pop();
}

uint32_t LetBinding::getId(Node n) const
{
  NodeIdMap::const_iterator it = d_letMap.find(n);
  if (it==d_letMap.end())
  {
    return 0;
  }
  return (*it).second;
}

}  // namespace proof
}  // namespace CVC4

