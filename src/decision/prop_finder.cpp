/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Propagation finder
 */

#include "decision/prop_finder.h"

namespace cvc5::internal {
namespace decision {

PropFinder::PropFinder(Env& env) : EnvObj(env) {}

PropFinder::~PropFinder() {}

void PropFinder::addAssertion(TNode n,
                              TNode skolem,
                              bool isLemma,
                              std::vector<TNode>& toPreregister)
{
  // TODO
}

void PropFinder::notifyActiveSkolemDefs(std::vector<TNode>& defs,
                                        std::vector<TNode>& toPreregister)
{
  // TODO
}

void PropFinder::notifyAsserted(TNode n, std::vector<TNode>& toPreregister)
{
  // TODO
  Node natom = n.getKind() == kind::NOT ? n[0] : n;
  toPreregister.push_back(natom);
}

}  // namespace decision
}  // namespace cvc5::internal
