/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * bag reduction.
 */

#include "theory/bags/bag_reduction.h"

#include "expr/bound_var_manager.h"
#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "util/rational.h"

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

BagReduction::BagReduction() {}

BagReduction::~BagReduction() {}

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over (may be distinct) elements in a bag, used
 * for axiomatizing the behavior of some term.
 * If there are multiple quantifiers, this variable should be the first one.
 */
struct FirstIndexVarAttributeId
{
};
typedef expr::Attribute<FirstIndexVarAttributeId, Node> FirstIndexVarAttribute;

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over (may be distinct) elements in a bag, used
 * for axiomatizing the behavior of some term.
 * This variable should be the second of multiple quantifiers.
 */
struct SecondIndexVarAttributeId
{
};
typedef expr::Attribute<SecondIndexVarAttributeId, Node>
    SecondIndexVarAttribute;

Node BagReduction::reduceFoldOperator(Node node, std::vector<Node>& asserts)
{
  Assert(node.getKind() == BAG_FOLD);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node f = node[0];
  Node t = node[1];
  Node A = node[2];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  // types
  TypeNode bagType = A.getType();
  TypeNode elementType = A.getType().getBagElementType();
  TypeNode integerType = nm->integerType();
  TypeNode ufType = nm->mkFunctionType(integerType, elementType);
  TypeNode resultType = t.getType();
  TypeNode combineType = nm->mkFunctionType(integerType, resultType);
  TypeNode unionDisjointType = nm->mkFunctionType(integerType, bagType);
  // skolem functions
  Node n = sm->mkSkolemFunction(SkolemFunId::BAGS_FOLD_CARD, integerType, A);
  Node uf = sm->mkSkolemFunction(SkolemFunId::BAGS_FOLD_ELEMENTS, ufType, A);
  Node unionDisjoint = sm->mkSkolemFunction(
      SkolemFunId::BAGS_FOLD_UNION_DISJOINT, unionDisjointType, A);
  Node combine = sm->mkSkolemFunction(
      SkolemFunId::BAGS_FOLD_COMBINE, combineType, {f, t, A});

  BoundVarManager* bvm = nm->getBoundVarManager();
  Node i =
      bvm->mkBoundVar<FirstIndexVarAttribute>(node, "i", nm->integerType());
  Node iList = nm->mkNode(BOUND_VAR_LIST, i);
  Node iMinusOne = nm->mkNode(SUB, i, one);
  Node uf_i = nm->mkNode(APPLY_UF, uf, i);
  Node combine_0 = nm->mkNode(APPLY_UF, combine, zero);
  Node combine_iMinusOne = nm->mkNode(APPLY_UF, combine, iMinusOne);
  Node combine_i = nm->mkNode(APPLY_UF, combine, i);
  Node combine_n = nm->mkNode(APPLY_UF, combine, n);
  Node unionDisjoint_0 = nm->mkNode(APPLY_UF, unionDisjoint, zero);
  Node unionDisjoint_iMinusOne = nm->mkNode(APPLY_UF, unionDisjoint, iMinusOne);
  Node unionDisjoint_i = nm->mkNode(APPLY_UF, unionDisjoint, i);
  Node unionDisjoint_n = nm->mkNode(APPLY_UF, unionDisjoint, n);
  Node combine_0_equal = combine_0.eqNode(t);
  Node combine_i_equal =
      combine_i.eqNode(nm->mkNode(APPLY_UF, f, uf_i, combine_iMinusOne));
  Node unionDisjoint_0_equal =
      unionDisjoint_0.eqNode(nm->mkConst(EmptyBag(bagType)));
  Node singleton = nm->mkNode(BAG_MAKE, uf_i, one);

  Node unionDisjoint_i_equal = unionDisjoint_i.eqNode(
      nm->mkNode(BAG_UNION_DISJOINT, singleton, unionDisjoint_iMinusOne));
  Node interval_i =
      nm->mkNode(AND, nm->mkNode(GEQ, i, one), nm->mkNode(LEQ, i, n));

  Node body_i =
      nm->mkNode(IMPLIES,
                 interval_i,
                 nm->mkNode(AND, combine_i_equal, unionDisjoint_i_equal));
  Node forAll_i = quantifiers::BoundedIntegers::mkBoundedForall(iList, body_i);
  Node nonNegative = nm->mkNode(GEQ, n, zero);
  Node unionDisjoint_n_equal = A.eqNode(unionDisjoint_n);
  asserts.push_back(forAll_i);
  asserts.push_back(combine_0_equal);
  asserts.push_back(unionDisjoint_0_equal);
  asserts.push_back(unionDisjoint_n_equal);
  asserts.push_back(nonNegative);
  return combine_n;
}

Node BagReduction::reduceCardOperator(Node node, std::vector<Node>& asserts)
{
  Assert(node.getKind() == BAG_CARD);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node A = node[0];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  // types
  TypeNode bagType = A.getType();
  TypeNode elementType = A.getType().getBagElementType();
  TypeNode integerType = nm->integerType();
  TypeNode ufType = nm->mkFunctionType(integerType, elementType);
  TypeNode cardinalityType = nm->mkFunctionType(integerType, integerType);
  TypeNode unionDisjointType = nm->mkFunctionType(integerType, bagType);
  // skolem functions
  Node n = sm->mkSkolemFunction(SkolemFunId::BAGS_CARD_N, integerType, A);
  Node uf = sm->mkSkolemFunction(SkolemFunId::BAGS_CARD_ELEMENTS, ufType, A);
  Node unionDisjoint = sm->mkSkolemFunction(
      SkolemFunId::BAGS_CARD_UNION_DISJOINT, unionDisjointType, A);
  Node cardinality = sm->mkSkolemFunction(
      SkolemFunId::BAGS_CARD_CARDINALITY, cardinalityType, A);

  BoundVarManager* bvm = nm->getBoundVarManager();
  Node i =
      bvm->mkBoundVar<FirstIndexVarAttribute>(node, "i", nm->integerType());
  Node j =
      bvm->mkBoundVar<SecondIndexVarAttribute>(node, "j", nm->integerType());
  Node iList = nm->mkNode(BOUND_VAR_LIST, i);
  Node jList = nm->mkNode(BOUND_VAR_LIST, j);
  Node iMinusOne = nm->mkNode(SUB, i, one);
  Node uf_i = nm->mkNode(APPLY_UF, uf, i);
  Node uf_j = nm->mkNode(APPLY_UF, uf, j);
  Node cardinality_0 = nm->mkNode(APPLY_UF, cardinality, zero);
  Node cardinality_iMinusOne = nm->mkNode(APPLY_UF, cardinality, iMinusOne);
  Node cardinality_i = nm->mkNode(APPLY_UF, cardinality, i);
  Node cardinality_n = nm->mkNode(APPLY_UF, cardinality, n);
  Node unionDisjoint_0 = nm->mkNode(APPLY_UF, unionDisjoint, zero);
  Node unionDisjoint_iMinusOne = nm->mkNode(APPLY_UF, unionDisjoint, iMinusOne);
  Node unionDisjoint_i = nm->mkNode(APPLY_UF, unionDisjoint, i);
  Node unionDisjoint_n = nm->mkNode(APPLY_UF, unionDisjoint, n);
  Node cardinality_0_equal = cardinality_0.eqNode(zero);
  Node uf_i_multiplicity = nm->mkNode(BAG_COUNT, uf_i, A);
  Node cardinality_i_equal = cardinality_i.eqNode(
      nm->mkNode(ADD, uf_i_multiplicity, cardinality_iMinusOne));
  Node unionDisjoint_0_equal =
      unionDisjoint_0.eqNode(nm->mkConst(EmptyBag(bagType)));
  Node bag = nm->mkNode(BAG_MAKE, uf_i, uf_i_multiplicity);

  Node unionDisjoint_i_equal = unionDisjoint_i.eqNode(
      nm->mkNode(BAG_UNION_DISJOINT, bag, unionDisjoint_iMinusOne));
  // 1 <= i <= n
  Node interval_i =
      nm->mkNode(AND, nm->mkNode(GEQ, i, one), nm->mkNode(LEQ, i, n));

  // i < j <= n
  Node interval_j =
      nm->mkNode(AND, nm->mkNode(LT, i, j), nm->mkNode(LEQ, j, n));
  // uf(i) != uf(j)
  Node uf_i_equals_uf_j = nm->mkNode(EQUAL, uf_i, uf_j);
  Node notEqual = nm->mkNode(EQUAL, uf_i, uf_j).negate();
  Node body_j = nm->mkNode(OR, interval_j.negate(), notEqual);
  Node forAll_j = quantifiers::BoundedIntegers::mkBoundedForall(jList, body_j);
  Node body_i = nm->mkNode(
      IMPLIES,
      interval_i,
      nm->mkNode(AND, cardinality_i_equal, unionDisjoint_i_equal, forAll_j));
  Node forAll_i = quantifiers::BoundedIntegers::mkBoundedForall(iList, body_i);
  Node nonNegative = nm->mkNode(GEQ, n, zero);
  Node unionDisjoint_n_equal = A.eqNode(unionDisjoint_n);
  asserts.push_back(forAll_i);
  asserts.push_back(cardinality_0_equal);
  asserts.push_back(unionDisjoint_0_equal);
  asserts.push_back(unionDisjoint_n_equal);
  asserts.push_back(nonNegative);
  return cardinality_n;
}

Node BagReduction::reduceAggregateOperator(Node node)
{
  Assert(node.getKind() == TABLE_AGGREGATE);
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node function = node[0];
  TypeNode elementType = function.getType().getArgTypes()[0];
  Node initialValue = node[1];
  Node A = node[2];
  ProjectOp op = node.getOperator().getConst<ProjectOp>();

  Node groupOp = nm->mkConst(TABLE_GROUP_OP, op);
  Node group = nm->mkNode(TABLE_GROUP, {groupOp, A});

  Node bag = bvm->mkBoundVar<FirstIndexVarAttribute>(
      group, "bag", nm->mkBagType(elementType));
  Node foldList = nm->mkNode(BOUND_VAR_LIST, bag);
  Node foldBody = nm->mkNode(BAG_FOLD, function, initialValue, bag);

  Node fold = nm->mkNode(LAMBDA, foldList, foldBody);
  Node map = nm->mkNode(BAG_MAP, fold, group);
  return map;
}

Node BagReduction::reduceProjectOperator(Node n)
{
  Assert(n.getKind() == TABLE_PROJECT);
  NodeManager* nm = NodeManager::currentNM();
  Node A = n[0];
  TypeNode elementType = A.getType().getBagElementType();
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = nm->mkConst(TUPLE_PROJECT_OP, projectOp);
  Node t = nm->mkBoundVar("t", elementType);
  Node projection = nm->mkNode(TUPLE_PROJECT, op, t);
  Node lambda = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, t), projection);
  Node setMap = nm->mkNode(BAG_MAP, lambda, A);
  return setMap;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
