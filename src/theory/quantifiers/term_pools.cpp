/*********************                                                        */
/*! \file term_pools.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for term enumeration
 **/

#include "theory/quantifiers/term_pools.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

void TermPoolDomain::initialize() { d_terms.clear(); }
void TermPoolDomain::add(Node n) { d_terms.insert(n); }

void TermPools::registerPool(Node p, const std::vector<Node>& initValue)
{
  TermPoolDomain& d = d_pools[p];
  d.initialize();
  d.d_terms.insert(initValue.begin(), initValue.end());
}

void TermPools::addToPool(Node n, Node p)
{
  TermPoolDomain& dom = getDomain(p);
  dom.add(n);
}

TermPoolDomain& TermPools::getDomain(Node p) { return d_pools[p]; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
