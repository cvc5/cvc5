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

std::set<Node> RelsUtils::computeTC(std::set<Node> rel_mem, Node rel)
{
  std::set<Node>::iterator mem_it = rel_mem.begin();
  std::map<Node, int> ele_num_map;
  std::set<Node> tc_rel_mem;

  while (mem_it != rel_mem.end())
  {
    Node fst = DatatypesUtils::nthElementOfTuple(*mem_it, 0);
    Node snd = DatatypesUtils::nthElementOfTuple(*mem_it, 1);
    std::set<Node> traversed;
    traversed.insert(fst);
    computeTC(rel, rel_mem, fst, snd, traversed, tc_rel_mem);
    mem_it++;
  }
  return tc_rel_mem;
}

static void RelsUtils::computeTC(Node rel,
                                 std::set<Node>& rel_mem,
                                 Node fst,
                                 Node snd,
                                 std::set<Node>& traversed,
                                 std::set<Node>& tc_rel_mem)
{
  tc_rel_mem.insert(constructPair(rel, fst, snd));
  if (traversed.find(snd) == traversed.end())
  {
    traversed.insert(snd);
  }
  else
  {
    return;
  }

  std::set<Node>::iterator mem_it = rel_mem.begin();
  while (mem_it != rel_mem.end())
  {
    Node new_fst = DatatypesUtils::nthElementOfTuple(*mem_it, 0);
    Node new_snd = DatatypesUtils::nthElementOfTuple(*mem_it, 1);
    if (snd == new_fst)
    {
      computeTC(rel, rel_mem, fst, new_snd, traversed, tc_rel_mem);
    }
    mem_it++;
  }
}

static Node RelsUtils::constructPair(Node rel, Node a, Node b)
{
  const DType& dt = rel.getType().getSetElementType().getDType();
  return NodeManager::currentNM()->mkNode(
      kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), a, b);
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5
