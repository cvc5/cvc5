/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for relations.
 */

#include "rels_utils.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "theory/datatypes/tuple_utils.h"

using namespace cvc5::theory::datatypes;

namespace cvc5 {
namespace theory {
namespace sets {

std::set<Node> RelsUtils::computeTC(const std::set<Node>& members, Node rel)
{
  std::set<Node>::iterator mem_it = members.begin();
  std::map<Node, int> ele_num_map;
  std::set<Node> tc_rel_mem;

  while (mem_it != members.end())
  {
    Node fst = TupleUtils::nthElementOfTuple(*mem_it, 0);
    Node snd = TupleUtils::nthElementOfTuple(*mem_it, 1);
    std::set<Node> traversed;
    traversed.insert(fst);
    computeTC(rel, members, fst, snd, traversed, tc_rel_mem);
    mem_it++;
  }
  return tc_rel_mem;
}

void RelsUtils::computeTC(Node rel,
                          const std::set<Node>& members,
                          Node a,
                          Node b,
                          std::set<Node>& traversed,
                          std::set<Node>& transitiveClosureMembers)
{
  transitiveClosureMembers.insert(constructPair(rel, a, b));
  if (traversed.find(b) != traversed.end())
  {
    return;
  }
  traversed.insert(b);
  std::set<Node>::iterator mem_it = members.begin();
  while (mem_it != members.end())
  {
    Node new_fst = TupleUtils::nthElementOfTuple(*mem_it, 0);
    Node new_snd = TupleUtils::nthElementOfTuple(*mem_it, 1);
    if (b == new_fst)
    {
      computeTC(rel, members, a, new_snd, traversed, transitiveClosureMembers);
    }
    mem_it++;
  }
}

Node RelsUtils::constructPair(Node rel, Node a, Node b)
{
  const DType& dt = rel.getType().getSetElementType().getDType();
  return NodeManager::currentNM()->mkNode(
      kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), a, b);
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5
