/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for data types.
 */

#include "tuple_utils.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

Node TupleUtils::nthElementOfTuple(Node tuple, int n_th)
{
  if (tuple.getKind() == APPLY_CONSTRUCTOR)
  {
    return tuple[n_th];
  }
  TypeNode tn = tuple.getType();
  const DType& dt = tn.getDType();
  return NodeManager::currentNM()->mkNode(
      APPLY_SELECTOR, dt[0].getSelectorInternal(tn, n_th), tuple);
}

Node TupleUtils::getTupleProjection(std::vector<uint32_t> indices, Node tuple)
{
  std::vector<TypeNode> tupleTypes = tuple.getType().getTupleTypes();
  std::vector<TypeNode> types;
  std::vector<Node> elements;
  for (uint32_t index : indices)
  {
    TypeNode type = tupleTypes[index];
    types.push_back(type);
  }
  NodeManager* nm = NodeManager::currentNM();
  TypeNode projectType = nm->mkTupleType(types);
  const DType& dt = projectType.getDType();
  elements.push_back(dt[0].getConstructor());
  const DType& tupleDType = tuple.getType().getDType();
  const DTypeConstructor& constructor = tupleDType[0];
  for (uint32_t index : indices)
  {
    Node selector = constructor[index].getSelector();
    Node element = nm->mkNode(kind::APPLY_SELECTOR, selector, tuple);
    elements.push_back(element);
  }
  Node ret = nm->mkNode(kind::APPLY_CONSTRUCTOR, elements);
  return ret;
}

std::vector<Node> TupleUtils::getTupleElements(Node tuple)
{
  Assert(tuple.getType().isTuple());
  size_t tupleLength = tuple.getType().getTupleLength();
  std::vector<Node> elements;
  for (size_t i = 0; i < tupleLength; i++)
  {
    elements.push_back(TupleUtils::nthElementOfTuple(tuple, i));
  }
  return elements;
}

std::vector<Node> TupleUtils::getTupleElements(Node tuple1, Node tuple2)
{
  std::vector<Node> elements;
  std::vector<Node> elementsA = getTupleElements(tuple1);
  size_t tuple1Length = tuple1.getType().getTupleLength();
  for (size_t i = 0; i < tuple1Length; i++)
  {
    elements.push_back(TupleUtils::nthElementOfTuple(tuple1, i));
  }

  size_t tuple2Length = tuple2.getType().getTupleLength();
  for (size_t i = 0; i < tuple2Length; i++)
  {
    elements.push_back(TupleUtils::nthElementOfTuple(tuple2, i));
  }
  return elements;
}

Node TupleUtils::constructTupleFromElements(TypeNode tupleType,
                                            const std::vector<Node>& elements,
                                            size_t start,
                                            size_t end)
{
  std::vector<Node> tupleElements;
  // add the constructor first
  Node constructor = tupleType.getDType()[0].getConstructor();
  tupleElements.push_back(constructor);
  // add the elements of the tuple
  for (size_t i = start; i <= end; i++)
  {
    tupleElements.push_back(elements[i]);
  }
  NodeManager* nm = NodeManager::currentNM();
  Node tuple = nm->mkNode(APPLY_CONSTRUCTOR, tupleElements);
  return tuple;
}

Node TupleUtils::concatTuples(TypeNode tupleType, Node tuple1, Node tuple2)
{
  std::vector<Node> tupleElements;
  // add the constructor first
  Node constructor = tupleType.getDType()[0].getConstructor();
  tupleElements.push_back(constructor);

  // add the flattened concatenation of the two tuples e1, e2
  std::vector<Node> elements = getTupleElements(tuple1, tuple2);
  tupleElements.insert(tupleElements.end(), elements.begin(), elements.end());

  // construct the returned tuple
  NodeManager* nm = NodeManager::currentNM();
  Node tuple = nm->mkNode(APPLY_CONSTRUCTOR, tupleElements);
  return tuple;
}

Node TupleUtils::reverseTuple(Node tuple)
{
  Assert(tuple.getType().isTuple());
  std::vector<Node> elements;
  std::vector<TypeNode> tuple_types = tuple.getType().getTupleTypes();
  std::reverse(tuple_types.begin(), tuple_types.end());
  TypeNode tn = NodeManager::currentNM()->mkTupleType(tuple_types);
  const DType& dt = tn.getDType();
  elements.push_back(dt[0].getConstructor());
  for (int i = tuple_types.size() - 1; i >= 0; --i)
  {
    elements.push_back(nthElementOfTuple(tuple, i));
  }
  return NodeManager::currentNM()->mkNode(APPLY_CONSTRUCTOR, elements);
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
