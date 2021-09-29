/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference generator utility.
 */

#include "inference_generator.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/uf/equality_engine.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace bags {

InferenceGenerator::InferenceGenerator(SolverState* state, InferenceManager* im)
    : d_state(state), d_im(im)
{
  d_nm = NodeManager::currentNM();
  d_sm = d_nm->getSkolemManager();
  d_true = d_nm->mkConst(true);
  d_zero = d_nm->mkConst(Rational(0));
  d_one = d_nm->mkConst(Rational(1));
}

InferInfo InferenceGenerator::nonNegativeCount(Node n, Node e)
{
  Assert(n.getType().isBag());
  Assert(e.getType() == n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_NON_NEGATIVE_COUNT);
  Node count = d_nm->mkNode(kind::BAG_COUNT, e, n);

  Node gte = d_nm->mkNode(kind::GEQ, count, d_zero);
  inferInfo.d_conclusion = gte;
  return inferInfo;
}

InferInfo InferenceGenerator::mkBag(Node n, Node e)
{
  Assert(n.getKind() == kind::MK_BAG);
  Assert(e.getType() == n.getType().getBagElementType());

  if (n[0] == e)
  {
    // TODO issue #78: refactor this with BagRewriter
    // (=> true (= (bag.count e (bag e c)) c))
    InferInfo inferInfo(d_im, InferenceId::BAGS_MK_BAG_SAME_ELEMENT);
    Node skolem = getSkolem(n, inferInfo);
    Node count = getMultiplicityTerm(e, skolem);
    inferInfo.d_conclusion = count.eqNode(n[1]);
    return inferInfo;
  }
  else
  {
    // (=>
    //   true
    //   (= (bag.count e (bag x c)) (ite (= e x) c 0)))
    InferInfo inferInfo(d_im, InferenceId::BAGS_MK_BAG);
    Node skolem = getSkolem(n, inferInfo);
    Node count = getMultiplicityTerm(e, skolem);
    Node same = d_nm->mkNode(kind::EQUAL, n[0], e);
    Node ite = d_nm->mkNode(kind::ITE, same, n[1], d_zero);
    Node equal = count.eqNode(ite);
    inferInfo.d_conclusion = equal;
    return inferInfo;
  }
}

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the distinct elements in a bag, used
 * for axiomatizing the behavior of some term.
 */
struct IndexVarAttributeId
{
};
typedef expr::Attribute<IndexVarAttributeId, Node> IndexVarAttribute;

struct BagsDeqAttributeId
{
};
typedef expr::Attribute<BagsDeqAttributeId, Node> BagsDeqAttribute;

InferInfo InferenceGenerator::bagDisequality(Node n)
{
  Assert(n.getKind() == kind::EQUAL && n[0].getType().isBag());

  Node A = n[0];
  Node B = n[1];

  InferInfo inferInfo(d_im, InferenceId::BAGS_DISEQUALITY);

  TypeNode elementType = A.getType().getBagElementType();
  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node element = bvm->mkBoundVar<BagsDeqAttribute>(n, elementType);
  Node skolem =
      d_sm->mkSkolem(element,
                     n,
                     "bag_disequal",
                     "an extensional lemma for disequality of two bags");

  Node countA = getMultiplicityTerm(skolem, A);
  Node countB = getMultiplicityTerm(skolem, B);

  Node disEqual = countA.eqNode(countB).notNode();

  inferInfo.d_premises.push_back(n.notNode());
  inferInfo.d_conclusion = disEqual;
  return inferInfo;
}

Node InferenceGenerator::getSkolem(Node& n, InferInfo& inferInfo)
{
  Node skolem = d_sm->mkPurifySkolem(n, "skolem_bag", "skolem bag");
  inferInfo.d_skolems[n] = skolem;
  return skolem;
}

InferInfo InferenceGenerator::empty(Node n, Node e)
{
  Assert(n.getKind() == kind::EMPTYBAG);
  Assert(e.getType() == n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_EMPTY);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node equal = count.eqNode(d_zero);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionDisjoint(Node n, Node e)
{
  Assert(n.getKind() == kind::UNION_DISJOINT && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_DISJOINT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node sum = d_nm->mkNode(kind::PLUS, countA, countB);
  Node equal = count.eqNode(sum);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionMax(Node n, Node e)
{
  Assert(n.getKind() == kind::UNION_MAX && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_MAX);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node gt = d_nm->mkNode(kind::GT, countA, countB);
  Node max = d_nm->mkNode(kind::ITE, gt, countA, countB);
  Node equal = count.eqNode(max);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::intersection(Node n, Node e)
{
  Assert(n.getKind() == kind::INTERSECTION_MIN && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_INTERSECTION_MIN);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node lt = d_nm->mkNode(kind::LT, countA, countB);
  Node min = d_nm->mkNode(kind::ITE, lt, countA, countB);
  Node equal = count.eqNode(min);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceSubtract(Node n, Node e)
{
  Assert(n.getKind() == kind::DIFFERENCE_SUBTRACT && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_SUBTRACT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node subtract = d_nm->mkNode(kind::MINUS, countA, countB);
  Node gte = d_nm->mkNode(kind::GEQ, countA, countB);
  Node difference = d_nm->mkNode(kind::ITE, gte, subtract, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceRemove(Node n, Node e)
{
  Assert(n.getKind() == kind::DIFFERENCE_REMOVE && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_REMOVE);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node notInB = d_nm->mkNode(kind::EQUAL, countB, d_zero);
  Node difference = d_nm->mkNode(kind::ITE, notInB, countA, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::duplicateRemoval(Node n, Node e)
{
  Assert(n.getKind() == kind::DUPLICATE_REMOVAL && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DUPLICATE_REMOVAL);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node gte = d_nm->mkNode(kind::GEQ, countA, d_one);
  Node ite = d_nm->mkNode(kind::ITE, gte, d_one, d_zero);
  Node equal = count.eqNode(ite);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

Node InferenceGenerator::getMultiplicityTerm(Node element, Node bag)
{
  Node count = d_nm->mkNode(kind::BAG_COUNT, element, bag);
  return count;
}

InferInfo InferenceGenerator::map(Node n, Node e)
{
  Assert(n.getKind() == kind::BAG_MAP && n[1].getType().isBag());
  Assert(e.getType() == n[1].getType().getBagElementType());
  Assert(n[0].getType().isFunction());

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP);
  Node f = n[0];
  Node A = n[1];
  // declare an uninterpreted function uf: Int -> T
  TypeNode codomainType = n[0].getType().getRangeType();
  TypeNode ufType = d_nm->mkFunctionType(d_nm->integerType(), codomainType);
  Node uf = d_sm->mkDummySkolem("map_uf", ufType);

  // declare uninterpreted function sum: Int -> Int
  TypeNode sumType =
      d_nm->mkFunctionType(d_nm->integerType(), d_nm->integerType());
  Node sum = d_sm->mkDummySkolem("map_sum", sumType);
  // guess the size of the preimage of e
  Node preImageSize =
      d_sm->mkDummySkolem("map_preimage_size", d_nm->integerType());


  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node i = bvm->mkBoundVar<IndexVarAttribute>(n, d_nm->integerType());
  Node iList = d_nm->mkNode(kind::BOUND_VAR_LIST, i);
  Node iPlusOne = d_nm->mkNode(kind::PLUS, i, d_one);
  Node iMinusOne = d_nm->mkNode(kind::MINUS, i, d_one);
  Node uf_i = d_nm->mkNode(kind::APPLY_UF, uf, i);
  Node f_uf_i = d_nm->mkNode(kind::APPLY_UF, f, uf_i);
  Node uf_iPlusOne = d_nm->mkNode(kind::APPLY_UF, uf, iPlusOne);
  Node uf_iMinusOne = d_nm->mkNode(kind::APPLY_UF, uf, iMinusOne);
  Node interval = d_nm->mkNode(kind::AND,
                               d_nm->mkNode(kind::GEQ, i, d_one),
                               d_nm->mkNode(kind::LEQ, i, preImageSize));
  Node sum_zero = d_nm->mkNode(kind::APPLY_UF, sum, d_zero);
  Node sum_i = d_nm->mkNode(kind::APPLY_UF, sum, i);
  Node sum_iPlusOne = d_nm->mkNode(kind::APPLY_UF, sum, iPlusOne);
  Node sum_iMinusOne = d_nm->mkNode(kind::APPLY_UF, sum, iMinusOne);
  Node count_iMinusOne = d_nm->mkNode(kind::BAG_COUNT, uf_iMinusOne, A);
  Node count_uf_i = d_nm->mkNode(kind::BAG_COUNT, uf_i, A);
  Node baseCase = d_nm->mkNode(Kind::EQUAL, sum_zero, d_zero);
  Node inductiveCase = d_nm->mkNode(
      Kind::EQUAL, sum_i, d_nm->mkNode(kind::PLUS, sum_iMinusOne, count_uf_i));
  Node f_iEqualE = d_nm->mkNode(kind::EQUAL, f_uf_i, e);
  Node greaterThanZero = d_nm->mkNode(kind::GT, count_uf_i, d_zero);
  Node andNode =
      d_nm->mkNode(kind::AND, f_iEqualE, greaterThanZero, inductiveCase);
  Node body = d_nm->mkNode(kind::OR, interval.negate(), andNode);
  Node forAll = d_nm->mkNode(kind::FORALL, iList, body);
  Node mapSkolem = getSkolem(n, inferInfo);
  Node countE = getMultiplicityTerm(e, mapSkolem);
  Node totalSum = d_nm->mkNode(kind::APPLY_UF, sum, preImageSize);
  Node totalSumEqualCountE = d_nm->mkNode(kind::EQUAL, totalSum, countE);
  TypeNode integerType = d_nm->integerType();

  Node conclusion =
      d_nm->mkNode(kind::AND, baseCase, forAll, totalSumEqualCountE);
  inferInfo.d_conclusion = conclusion;
  return inferInfo;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
