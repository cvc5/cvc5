/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * set reduction.
 */

#include "theory/sets/set_reduction.h"

#include "expr/bound_var_manager.h"
#include "expr/emptyset.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes//project_op.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "util/rational.h"

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sets {

SetReduction::SetReduction() {}

SetReduction::~SetReduction() {}

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over (may be distinct) elements in a set, used
 * for axiomatizing the behavior of some term.
 * If there are multiple quantifiers, this variable should be the first one.
 */
struct FirstIndexVarAttributeId
{
};
typedef expr::Attribute<FirstIndexVarAttributeId, Node> FirstIndexVarAttribute;

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over (may be distinct) elements in a set, used
 * for axiomatizing the behavior of some term.
 * This variable should be the second of multiple quantifiers.
 */
struct SecondIndexVarAttributeId
{
};
typedef expr::Attribute<SecondIndexVarAttributeId, Node>
    SecondIndexVarAttribute;

Node SetReduction::reduceFoldOperator(Node node, std::vector<Node>& asserts)
{
  Assert(node.getKind() == Kind::SET_FOLD);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node f = node[0];
  Node t = node[1];
  Node A = node[2];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  // skolem functions
  Node n = sm->mkSkolemFunction(SkolemId::SETS_FOLD_CARD, A);
  Node uf = sm->mkSkolemFunction(SkolemId::SETS_FOLD_ELEMENTS, A);
  Node unionNode = sm->mkSkolemFunction(SkolemId::SETS_FOLD_UNION, A);
  Node combine = sm->mkSkolemFunction(SkolemId::SETS_FOLD_COMBINE, {f, t, A});

  BoundVarManager* bvm = nm->getBoundVarManager();
  Node i =
      bvm->mkBoundVar<FirstIndexVarAttribute>(node, "i", nm->integerType());
  Node iList = nm->mkNode(Kind::BOUND_VAR_LIST, i);
  Node iMinusOne = nm->mkNode(Kind::SUB, i, one);
  Node uf_i = nm->mkNode(Kind::APPLY_UF, uf, i);
  Node combine_0 = nm->mkNode(Kind::APPLY_UF, combine, zero);
  Node combine_iMinusOne = nm->mkNode(Kind::APPLY_UF, combine, iMinusOne);
  Node combine_i = nm->mkNode(Kind::APPLY_UF, combine, i);
  Node combine_n = nm->mkNode(Kind::APPLY_UF, combine, n);
  Node union_0 = nm->mkNode(Kind::APPLY_UF, unionNode, zero);
  Node union_iMinusOne = nm->mkNode(Kind::APPLY_UF, unionNode, iMinusOne);
  Node union_i = nm->mkNode(Kind::APPLY_UF, unionNode, i);
  Node union_n = nm->mkNode(Kind::APPLY_UF, unionNode, n);
  Node combine_0_equal = combine_0.eqNode(t);
  Node combine_i_equal =
      combine_i.eqNode(nm->mkNode(Kind::APPLY_UF, f, uf_i, combine_iMinusOne));
  Node union_0_equal = union_0.eqNode(nm->mkConst(EmptySet(A.getType())));
  Node singleton = nm->mkNode(Kind::SET_SINGLETON, uf_i);

  Node union_i_equal =
      union_i.eqNode(nm->mkNode(Kind::SET_UNION, singleton, union_iMinusOne));
  Node interval_i = nm->mkNode(
      Kind::AND, nm->mkNode(Kind::GEQ, i, one), nm->mkNode(Kind::LEQ, i, n));

  Node body_i =
      nm->mkNode(Kind::IMPLIES,
                 interval_i,
                 nm->mkNode(Kind::AND, combine_i_equal, union_i_equal));
  Node forAll_i =
      quantifiers::BoundedIntegers::mkBoundedForall(nm, iList, body_i);
  Node nonNegative = nm->mkNode(Kind::GEQ, n, zero);
  Node union_n_equal = A.eqNode(union_n);
  asserts.push_back(forAll_i);
  asserts.push_back(combine_0_equal);
  asserts.push_back(union_0_equal);
  asserts.push_back(union_n_equal);
  asserts.push_back(nonNegative);
  return combine_n;
}

Node SetReduction::reduceAggregateOperator(Node node)
{
  Assert(node.getKind() == Kind::RELATION_AGGREGATE);
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node function = node[0];
  TypeNode elementType = function.getType().getArgTypes()[0];
  Node initialValue = node[1];
  Node A = node[2];

  ProjectOp op = node.getOperator().getConst<ProjectOp>();
  Node groupOp = nm->mkConst(Kind::RELATION_GROUP_OP, op);
  Node group = nm->mkNode(Kind::RELATION_GROUP, {groupOp, A});

  Node set = bvm->mkBoundVar<FirstIndexVarAttribute>(
      group, "set", nm->mkSetType(elementType));
  Node foldList = nm->mkNode(Kind::BOUND_VAR_LIST, set);
  Node foldBody = nm->mkNode(Kind::SET_FOLD, function, initialValue, set);

  Node fold = nm->mkNode(Kind::LAMBDA, foldList, foldBody);
  Node map = nm->mkNode(Kind::SET_MAP, fold, group);
  return map;
}

Node SetReduction::reduceProjectOperator(Node n)
{
  Assert(n.getKind() == Kind::RELATION_PROJECT);
  NodeManager* nm = NodeManager::currentNM();
  Node A = n[0];
  TypeNode elementType = A.getType().getSetElementType();
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = nm->mkConst(Kind::TUPLE_PROJECT_OP, projectOp);
  Node t = NodeManager::mkBoundVar("t", elementType);
  Node projection = nm->mkNode(Kind::TUPLE_PROJECT, op, t);
  Node lambda =
      nm->mkNode(Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, t), projection);
  Node setMap = nm->mkNode(Kind::SET_MAP, lambda, A);
  return setMap;
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
