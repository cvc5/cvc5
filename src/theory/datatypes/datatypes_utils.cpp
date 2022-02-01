/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for data types.
 */

#include "datatypes_utils.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace datatypes {

Node DatatypesUtils::nthElementOfTuple(Node tuple, int n_th)
{
  if (tuple.getKind() == APPLY_CONSTRUCTOR)
  {
    return tuple[n_th];
  }
  TypeNode tn = tuple.getType();
  const DType& dt = tn.getDType();
  return NodeManager::currentNM()->mkNode(
      APPLY_SELECTOR_TOTAL, dt[0].getSelectorInternal(tn, n_th), tuple);
}

std::vector<Node> DatatypesUtils::getTupleElements(Node tuple)
{
  Assert(tuple.getType().isTuple());
  size_t tupleLength = tuple.getType().getTupleLength();
  std::vector<Node> elements;
  for (size_t i = 0; i < tupleLength; i++)
  {
    elements.push_back(DatatypesUtils::nthElementOfTuple(tuple, i));
  }
  return elements;
}

std::vector<Node> DatatypesUtils::getTupleElements(Node tuple1, Node tuple2)
{
  std::vector<Node> elements;
  std::vector<Node> elementsA = getTupleElements(tuple1);
  size_t tuple1Length = tuple1.getType().getTupleLength();
  for (size_t i = 0; i < tuple1Length; i++)
  {
    elements.push_back(DatatypesUtils::nthElementOfTuple(tuple1, i));
  }

  size_t tuple2Length = tuple2.getType().getTupleLength();
  for (size_t i = 0; i < tuple2Length; i++)
  {
    elements.push_back(DatatypesUtils::nthElementOfTuple(tuple2, i));
  }
  return elements;
}

Node DatatypesUtils::reverseTuple(Node tuple)
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
}  // namespace cvc5
