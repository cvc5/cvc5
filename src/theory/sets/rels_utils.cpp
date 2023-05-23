/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/set_reduction.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;
using namespace cvc5::internal::theory::sets;

namespace cvc5::internal {
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
      APPLY_CONSTRUCTOR, dt[0].getConstructor(), a, b);
}

Node RelsUtils::evaluateGroup(TNode n)
{
  Assert(n.getKind() == RELATION_GROUP);

  NodeManager* nm = NodeManager::currentNM();

  Node A = n[0];
  TypeNode setType = A.getType();
  TypeNode partitionType = n.getType();

  if (A.getKind() == SET_EMPTY)
  {
    // return a nonempty partition
    return nm->mkNode(SET_SINGLETON, A);
  }

  std::vector<uint32_t> indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  std::set<Node> elements = NormalForm::getElementsFromNormalConstant(A);
  Trace("sets-group") << "elements: " << elements << std::endl;
  // a simple map from elements to equivalent classes with this invariant:
  // each key element must appear exactly once in one of the values.
  std::map<Node, std::set<Node>> sets;
  std::set<Node> emptyClass;
  for (const Node& element : elements)
  {
    // initially each singleton element is an equivalence class
    sets[element] = {element};
  }
  for (std::set<Node>::iterator i = elements.begin(); i != elements.end(); ++i)
  {
    Node iElement = *i;
    if (sets[iElement].empty())
    {
      // skip this element since its equivalent class has already been processed
      continue;
    }
    std::set<Node>::iterator j = i;
    ++j;
    while (j != elements.end())
    {
      Node jElement = *j;
      if (TupleUtils::sameProjection(indices, iElement, jElement))
      {
        // add element j to the equivalent class
        sets[iElement].insert(jElement);
        // mark the equivalent class of j as processed
        sets[jElement] = emptyClass;
      }
      ++j;
    }
  }

  // construct the partition parts
  std::set<Node> parts;
  for (std::pair<Node, std::set<Node>> pair : sets)
  {
    const std::set<Node>& eqc = pair.second;
    if (eqc.empty())
    {
      continue;
    }
    Node part = NormalForm::elementsToSet(eqc, setType);
    parts.insert(part);
  }
  Node ret = NormalForm::elementsToSet(parts, partitionType);
  Trace("sets-group") << "ret: " << ret << std::endl;
  return ret;
}

Node RelsUtils::evaluateRelationAggregate(TNode n)
{
  Assert(n.getKind() == RELATION_AGGREGATE);
  if (!(n[1].isConst() && n[2].isConst()))
  {
    // we can't proceed further.
    return n;
  }

  Node reduction = SetReduction::reduceAggregateOperator(n);
  return reduction;
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
