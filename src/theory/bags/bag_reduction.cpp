/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  Assert(node.getKind() == Kind::BAG_FOLD);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node f = node[0];
  Node t = node[1];
  Node A = node[2];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  // skolem functions
  Node n = sm->mkSkolemFunction(SkolemId::BAGS_FOLD_CARD, A);
  Node elements = sm->mkSkolemFunction(SkolemId::BAGS_FOLD_ELEMENTS, A);
  Node unionDisjoint =
      sm->mkSkolemFunction(SkolemId::BAGS_FOLD_UNION_DISJOINT, A);
  Node combine = sm->mkSkolemFunction(SkolemId::BAGS_FOLD_COMBINE, {f, t, A});

  BoundVarManager* bvm = nm->getBoundVarManager();
  Node i =
      bvm->mkBoundVar<FirstIndexVarAttribute>(node, "i", nm->integerType());
  Node iList = nm->mkNode(Kind::BOUND_VAR_LIST, i);
  Node iMinusOne = nm->mkNode(Kind::SUB, i, one);
  Node elements_i = nm->mkNode(Kind::APPLY_UF, elements, i);
  Node combine_0 = nm->mkNode(Kind::APPLY_UF, combine, zero);
  Node combine_iMinusOne = nm->mkNode(Kind::APPLY_UF, combine, iMinusOne);
  Node combine_i = nm->mkNode(Kind::APPLY_UF, combine, i);
  Node combine_n = nm->mkNode(Kind::APPLY_UF, combine, n);
  Node unionDisjoint_0 = nm->mkNode(Kind::APPLY_UF, unionDisjoint, zero);
  Node unionDisjoint_iMinusOne =
      nm->mkNode(Kind::APPLY_UF, unionDisjoint, iMinusOne);
  Node unionDisjoint_i = nm->mkNode(Kind::APPLY_UF, unionDisjoint, i);
  Node unionDisjoint_n = nm->mkNode(Kind::APPLY_UF, unionDisjoint, n);
  Node combine_0_equal = combine_0.eqNode(t);
  Node combine_i_equal = combine_i.eqNode(
      nm->mkNode(Kind::APPLY_UF, f, elements_i, combine_iMinusOne));
  Node unionDisjoint_0_equal =
      unionDisjoint_0.eqNode(nm->mkConst(EmptyBag(A.getType())));
  Node singleton = nm->mkNode(Kind::BAG_MAKE, elements_i, one);

  Node unionDisjoint_i_equal = unionDisjoint_i.eqNode(
      nm->mkNode(Kind::BAG_UNION_DISJOINT, singleton, unionDisjoint_iMinusOne));
  Node interval_i = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, i, one), nm->mkNode(Kind::LEQ, i, n));

  Node body_i =
      nm->mkNode(Kind::IMPLIES,
                 interval_i,
                 nm->mkNode(Kind::AND, combine_i_equal, unionDisjoint_i_equal));
  Node forAll_i = quantifiers::BoundedIntegers::mkBoundedForall(iList, body_i);
  Node nonNegative = nm->mkNode(Kind::GEQ, n, zero);
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
  Assert(node.getKind() == Kind::BAG_CARD);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node A = node[0];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  // types
  TypeNode bagType = A.getType();
  // skolem functions
  Node n = sm->mkSkolemFunction(SkolemId::BAGS_DISTINCT_ELEMENTS_SIZE, A);
  Node elements = sm->mkSkolemFunction(SkolemId::BAGS_DISTINCT_ELEMENTS, A);
  Node unionDisjoint =
      sm->mkSkolemFunction(SkolemId::BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT, A);
  Node combine = sm->mkSkolemFunction(SkolemId::BAGS_CARD_COMBINE, A);

  BoundVarManager* bvm = nm->getBoundVarManager();
  Node i =
      bvm->mkBoundVar<FirstIndexVarAttribute>(node, "i", nm->integerType());
  Node j =
      bvm->mkBoundVar<SecondIndexVarAttribute>(node, "j", nm->integerType());
  Node iList = nm->mkNode(Kind::BOUND_VAR_LIST, i);
  Node jList = nm->mkNode(Kind::BOUND_VAR_LIST, j);
  Node iMinusOne = nm->mkNode(Kind::SUB, i, one);
  Node elements_i = nm->mkNode(Kind::APPLY_UF, elements, i);
  Node elements_j = nm->mkNode(Kind::APPLY_UF, elements, j);
  Node combine_0 = nm->mkNode(Kind::APPLY_UF, combine, zero);
  Node combine_iMinusOne = nm->mkNode(Kind::APPLY_UF, combine, iMinusOne);
  Node combine_i = nm->mkNode(Kind::APPLY_UF, combine, i);
  Node combine_n = nm->mkNode(Kind::APPLY_UF, combine, n);
  Node unionDisjoint_0 = nm->mkNode(Kind::APPLY_UF, unionDisjoint, zero);
  Node unionDisjoint_iMinusOne =
      nm->mkNode(Kind::APPLY_UF, unionDisjoint, iMinusOne);
  Node unionDisjoint_i = nm->mkNode(Kind::APPLY_UF, unionDisjoint, i);
  Node unionDisjoint_n = nm->mkNode(Kind::APPLY_UF, unionDisjoint, n);
  Node combine_0_equal = combine_0.eqNode(zero);
  Node elements_i_multiplicity = nm->mkNode(Kind::BAG_COUNT, elements_i, A);
  Node combine_i_equal = combine_i.eqNode(
      nm->mkNode(Kind::ADD, elements_i_multiplicity, combine_iMinusOne));
  Node unionDisjoint_0_equal =
      unionDisjoint_0.eqNode(nm->mkConst(EmptyBag(bagType)));
  Node bag = nm->mkNode(Kind::BAG_MAKE, elements_i, elements_i_multiplicity);

  Node unionDisjoint_i_equal = unionDisjoint_i.eqNode(
      nm->mkNode(Kind::BAG_UNION_DISJOINT, bag, unionDisjoint_iMinusOne));
  // 1 <= i <= n
  Node interval_i = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, i, one), nm->mkNode(Kind::LEQ, i, n));

  // i < j <= n
  Node interval_j = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::LT, i, j), nm->mkNode(Kind::LEQ, j, n));
  // elements(i) != elements(j)
  Node elements_i_equals_elements_j =
      nm->mkNode(Kind::EQUAL, elements_i, elements_j);
  Node notEqual = nm->mkNode(Kind::EQUAL, elements_i, elements_j).negate();
  Node body_j = nm->mkNode(Kind::OR, interval_j.negate(), notEqual);
  Node forAll_j = quantifiers::BoundedIntegers::mkBoundedForall(jList, body_j);
  Node body_i = nm->mkNode(
      Kind::IMPLIES,
      interval_i,
      nm->mkNode(Kind::AND, combine_i_equal, unionDisjoint_i_equal, forAll_j));
  Node forAll_i = quantifiers::BoundedIntegers::mkBoundedForall(iList, body_i);
  Node nonNegative = nm->mkNode(Kind::GEQ, n, zero);
  Node unionDisjoint_n_equal = A.eqNode(unionDisjoint_n);
  asserts.push_back(forAll_i);
  asserts.push_back(combine_0_equal);
  asserts.push_back(unionDisjoint_0_equal);
  asserts.push_back(unionDisjoint_n_equal);
  asserts.push_back(nonNegative);
  return combine_n;
}

Node BagReduction::reduceAggregateOperator(Node node)
{
  Assert(node.getKind() == Kind::TABLE_AGGREGATE);
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node function = node[0];
  TypeNode elementType = function.getType().getArgTypes()[0];
  Node initialValue = node[1];
  Node A = node[2];
  ProjectOp op = node.getOperator().getConst<ProjectOp>();

  Node groupOp = nm->mkConst(Kind::TABLE_GROUP_OP, op);
  Node group = nm->mkNode(Kind::TABLE_GROUP, {groupOp, A});

  Node bag = bvm->mkBoundVar<FirstIndexVarAttribute>(
      group, "bag", nm->mkBagType(elementType));
  Node foldList = nm->mkNode(Kind::BOUND_VAR_LIST, bag);
  Node foldBody = nm->mkNode(Kind::BAG_FOLD, function, initialValue, bag);

  Node fold = nm->mkNode(Kind::LAMBDA, foldList, foldBody);
  Node map = nm->mkNode(Kind::BAG_MAP, fold, group);
  return map;
}

Node BagReduction::reduceProjectOperator(Node n)
{
  Assert(n.getKind() == Kind::TABLE_PROJECT);
  NodeManager* nm = NodeManager::currentNM();
  Node A = n[0];
  TypeNode elementType = A.getType().getBagElementType();
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = nm->mkConst(Kind::TUPLE_PROJECT_OP, projectOp);
  Node t = nm->mkBoundVar("t", elementType);
  Node projection = nm->mkNode(Kind::TUPLE_PROJECT, op, t);
  Node lambda =
      nm->mkNode(Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, t), projection);
  Node setMap = nm->mkNode(Kind::BAG_MAP, lambda, A);
  return setMap;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
