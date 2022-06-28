/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include "theory/datatypes/tuple_utils.h"
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
  Assert(node.getKind() == SET_FOLD);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node f = node[0];
  Node t = node[1];
  Node A = node[2];
  Node zero = nm->mkConstInt(Rational(0));
  Node one = nm->mkConstInt(Rational(1));
  // types
  TypeNode setType = A.getType();
  TypeNode elementType = A.getType().getSetElementType();
  TypeNode integerType = nm->integerType();
  TypeNode ufType = nm->mkFunctionType(integerType, elementType);
  TypeNode resultType = t.getType();
  TypeNode combineType = nm->mkFunctionType(integerType, resultType);
  TypeNode unionType = nm->mkFunctionType(integerType, setType);
  // skolem functions
  Node n = sm->mkSkolemFunction(SkolemFunId::SETS_FOLD_CARD, integerType, A);
  Node uf = sm->mkSkolemFunction(SkolemFunId::SETS_FOLD_ELEMENTS, ufType, A);
  Node unionNode =
      sm->mkSkolemFunction(SkolemFunId::SETS_FOLD_UNION, unionType, A);
  Node combine = sm->mkSkolemFunction(
      SkolemFunId::SETS_FOLD_COMBINE, combineType, {f, t, A});

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
  Node union_0 = nm->mkNode(APPLY_UF, unionNode, zero);
  Node union_iMinusOne = nm->mkNode(APPLY_UF, unionNode, iMinusOne);
  Node union_i = nm->mkNode(APPLY_UF, unionNode, i);
  Node union_n = nm->mkNode(APPLY_UF, unionNode, n);
  Node combine_0_equal = combine_0.eqNode(t);
  Node combine_i_equal =
      combine_i.eqNode(nm->mkNode(APPLY_UF, f, uf_i, combine_iMinusOne));
  Node union_0_equal = union_0.eqNode(nm->mkConst(EmptySet(setType)));
  Node singleton = nm->mkNode(SET_SINGLETON, uf_i);

  Node union_i_equal =
      union_i.eqNode(nm->mkNode(SET_UNION, singleton, union_iMinusOne));
  Node interval_i =
      nm->mkNode(AND, nm->mkNode(GEQ, i, one), nm->mkNode(LEQ, i, n));

  Node body_i = nm->mkNode(
      IMPLIES, interval_i, nm->mkNode(AND, combine_i_equal, union_i_equal));
  Node forAll_i = quantifiers::BoundedIntegers::mkBoundedForall(iList, body_i);
  Node nonNegative = nm->mkNode(GEQ, n, zero);
  Node union_n_equal = A.eqNode(union_n);
  asserts.push_back(forAll_i);
  asserts.push_back(combine_0_equal);
  asserts.push_back(union_0_equal);
  asserts.push_back(union_n_equal);
  asserts.push_back(nonNegative);
  return combine_n;
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
