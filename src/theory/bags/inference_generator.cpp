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
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "theory/bags/bags_utils.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/uf/equality_engine.h"
#include "util/rational.h"

using namespace cvc5::kind;
using namespace cvc5::theory::datatypes;

namespace cvc5 {
namespace theory {
namespace bags {

InferenceGenerator::InferenceGenerator(SolverState* state, InferenceManager* im)
    : d_state(state), d_im(im)
{
  d_nm = NodeManager::currentNM();
  d_sm = d_nm->getSkolemManager();
  d_true = d_nm->mkConst(true);
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

InferInfo InferenceGenerator::nonNegativeCount(Node n, Node e)
{
  Assert(n.getType().isBag());
  Assert(e.getType().isSubtypeOf(n.getType().getBagElementType()));

  InferInfo inferInfo(d_im, InferenceId::BAGS_NON_NEGATIVE_COUNT);
  Node count = d_nm->mkNode(BAG_COUNT, e, n);
  Node gte = d_nm->mkNode(GEQ, count, d_zero);
  inferInfo.d_conclusion = gte;
  return inferInfo;
}

InferInfo InferenceGenerator::nonNegativeCardinality(Node n)
{
  InferInfo inferInfo(d_im, InferenceId::BAGS_NON_NEGATIVE_COUNT);
  Node gte = d_nm->mkNode(GEQ, n, d_zero);
  inferInfo.d_conclusion = gte;
  return inferInfo;
}

InferInfo InferenceGenerator::bagMake(Node n)
{
  Assert(n.getKind() == BAG_MAKE);
  /*
   * (or
   *   (and (<  c 1) (= (bag x c) (as bag.empty (Bag E))))
   *   (and (>= c 1) (not (= (bag x c) (as bag.empty (Bag E))))
   */
  Node x = n[0];
  Node c = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_BAG_MAKE_SPLIT);
  Node empty = d_nm->mkConst(EmptyBag(n.getType()));
  Node equal = d_nm->mkNode(EQUAL, n, empty);
  Node geq = d_nm->mkNode(GEQ, c, d_one);
  Node isEmpty = geq.notNode().andNode(equal);
  Node isNotEmpty = geq.andNode(equal.notNode());
  Node orNode = isEmpty.orNode(isNotEmpty);
  inferInfo.d_conclusion = orNode;
  return inferInfo;
}

InferInfo InferenceGenerator::bagMake(Node n, Node e)
{
  Assert(n.getKind() == BAG_MAKE);
  Assert(e.getType().isSubtypeOf(n.getType().getBagElementType()));

  /*
   * (ite (and (= e x) (>= c 1))
   *   (= (bag.count e skolem) c)
   *   (= (bag.count e skolem) 0))
   */
  Node x = n[0];
  Node c = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_BAG_MAKE);
  Node same = d_nm->mkNode(EQUAL, e, x);
  Node geq = d_nm->mkNode(GEQ, c, d_one);
  Node andNode = same.andNode(geq);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);
  Node equalC = d_nm->mkNode(EQUAL, count, c);
  Node equalZero = d_nm->mkNode(EQUAL, count, d_zero);
  Node ite = d_nm->mkNode(ITE, andNode, equalC, equalZero);
  inferInfo.d_conclusion = ite;
  return inferInfo;
}

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the distinct elements in a bag, used
 * for axiomatizing the behavior of some term.
 */
struct FirstIndexVarAttributeId
{
};
typedef expr::Attribute<FirstIndexVarAttributeId, Node> FirstIndexVarAttribute;

/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the distinct elements in a bag, used
 * for axiomatizing the behavior of some term.
 */
struct SecondIndexVarAttributeId
{
};
typedef expr::Attribute<SecondIndexVarAttributeId, Node>
    SecondIndexVarAttribute;

struct BagsDeqAttributeId
{
};
typedef expr::Attribute<BagsDeqAttributeId, Node> BagsDeqAttribute;

InferInfo InferenceGenerator::bagDisequality(Node n)
{
  Assert(n.getKind() == EQUAL && n[0].getType().isBag());

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
  Assert(n.getKind() == BAG_EMPTY);
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
  Assert(n.getKind() == BAG_UNION_DISJOINT && n[0].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[0].getType().getBagElementType()));

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_DISJOINT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node sum = d_nm->mkNode(ADD, countA, countB);
  Node equal = count.eqNode(sum);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionMax(Node n, Node e)
{
  Assert(n.getKind() == BAG_UNION_MAX && n[0].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[0].getType().getBagElementType()));

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_MAX);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node gt = d_nm->mkNode(GT, countA, countB);
  Node max = d_nm->mkNode(ITE, gt, countA, countB);
  Node equal = count.eqNode(max);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::intersection(Node n, Node e)
{
  Assert(n.getKind() == BAG_INTER_MIN && n[0].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[0].getType().getBagElementType()));

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_INTERSECTION_MIN);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node lt = d_nm->mkNode(LT, countA, countB);
  Node min = d_nm->mkNode(ITE, lt, countA, countB);
  Node equal = count.eqNode(min);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceSubtract(Node n, Node e)
{
  Assert(n.getKind() == BAG_DIFFERENCE_SUBTRACT && n[0].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[0].getType().getBagElementType()));

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_SUBTRACT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node subtract = d_nm->mkNode(SUB, countA, countB);
  Node gte = d_nm->mkNode(GEQ, countA, countB);
  Node difference = d_nm->mkNode(ITE, gte, subtract, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::differenceRemove(Node n, Node e)
{
  Assert(n.getKind() == BAG_DIFFERENCE_REMOVE && n[0].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[0].getType().getBagElementType()));

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_REMOVE);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node notInB = d_nm->mkNode(LEQ, countB, d_zero);
  Node difference = d_nm->mkNode(ITE, notInB, countA, d_zero);
  Node equal = count.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::duplicateRemoval(Node n, Node e)
{
  Assert(n.getKind() == BAG_DUPLICATE_REMOVAL && n[0].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[0].getType().getBagElementType()));

  Node A = n[0];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DUPLICATE_REMOVAL);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node gte = d_nm->mkNode(GEQ, countA, d_one);
  Node ite = d_nm->mkNode(ITE, gte, d_one, d_zero);
  Node equal = count.eqNode(ite);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::cardEmpty(const std::pair<Node, Node>& pair,
                                        Node n)
{
  Assert(pair.first.getKind() == BAG_CARD);
  Assert(n.getKind() == BAG_EMPTY && n.getType() == pair.first[0].getType());
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD);
  Node premise = pair.first[0].eqNode(n);
  Node conclusion = pair.second.eqNode(d_zero);
  inferInfo.d_conclusion = premise.notNode().orNode(conclusion);
  return inferInfo;
}

InferInfo InferenceGenerator::cardBagMake(const std::pair<Node, Node>& pair,
                                          Node n)
{
  Assert(pair.first.getKind() == BAG_CARD);
  Assert(n.getKind() == BAG_MAKE && n.getType() == pair.first[0].getType());
  //(=>
  //  (and (= A (bag x c)) (>= 0 c))
  //  (= (bag.card A) c))
  Node c = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD);
  Node nonNegative = d_nm->mkNode(GEQ, c, d_zero);
  Node premise = pair.first[0].eqNode(n).andNode(nonNegative);
  Node conclusion = pair.second.eqNode(c);
  inferInfo.d_conclusion = premise.notNode().orNode(conclusion);
  return inferInfo;
}

InferInfo InferenceGenerator::cardUnionDisjoint(Node premise,
                                                Node parent,
                                                const std::set<Node>& children)
{
  Assert(premise.getType().isBoolean());
  Assert(!children.empty());
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD);

  std::set<Node>::iterator it = children.begin();
  Node child = *it;
  d_state->registerBag(child);
  Node unionDisjoints = child;
  Node card = d_nm->mkNode(BAG_CARD, child);
  std::vector<Node> lemmas;
  lemmas.push_back(d_state->registerCardinalityTerm(card));
  Node sum = d_state->getCardinalitySkolem(card);
  ++it;
  while (it != children.end())
  {
    child = *it;
    d_state->registerBag(child);
    unionDisjoints =
        d_nm->mkNode(kind::BAG_UNION_DISJOINT, unionDisjoints, child);
    card = d_nm->mkNode(BAG_CARD, child);
    lemmas.push_back(d_state->registerCardinalityTerm(card));
    d_state->getCardinalitySkolem(card);
    Node skolem = d_state->getCardinalitySkolem(card);
    sum = d_nm->mkNode(ADD, sum, skolem);
    ++it;
  }
  Node parentCard = d_nm->mkNode(BAG_CARD, parent);
  lemmas.push_back(d_state->registerCardinalityTerm(parentCard));
  Node parentSkolem = d_state->getCardinalitySkolem(parentCard);

  Node bags = parent.eqNode(unionDisjoints);
  lemmas.push_back(bags);
  Node cards = parentSkolem.eqNode(sum);
  lemmas.push_back(cards);
  Node conclusion = d_nm->mkNode(AND, lemmas);
  inferInfo.d_conclusion = premise.notNode().orNode(conclusion);
  return inferInfo;
}

Node InferenceGenerator::getMultiplicityTerm(Node element, Node bag)
{
  Node count = d_nm->mkNode(BAG_COUNT, element, bag);
  return count;
}

std::tuple<InferInfo, Node, Node> InferenceGenerator::mapDown(Node n, Node e)
{
  Assert(n.getKind() == BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);
  Assert(e.getType() == n[0].getType().getRangeType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_DOWN);

  Node f = n[0];
  Node A = n[1];
  // declare an uninterpreted function uf: Int -> T
  TypeNode domainType = f.getType().getArgTypes()[0];
  TypeNode ufType = d_nm->mkFunctionType(d_nm->integerType(), domainType);
  Node uf =
      d_sm->mkSkolemFunction(SkolemFunId::BAGS_MAP_PREIMAGE, ufType, {n, e});

  // declare uninterpreted function sum: Int -> Int
  TypeNode sumType =
      d_nm->mkFunctionType(d_nm->integerType(), d_nm->integerType());
  Node sum = d_sm->mkSkolemFunction(SkolemFunId::BAGS_MAP_SUM, sumType, {n, e});

  // (= (sum 0) 0)
  Node sum_zero = d_nm->mkNode(APPLY_UF, sum, d_zero);
  Node baseCase = d_nm->mkNode(EQUAL, sum_zero, d_zero);

  // guess the size of the preimage of e
  Node preImageSize = d_sm->mkDummySkolem("preImageSize", d_nm->integerType());

  // (= (sum preImageSize) (bag.count e skolem))
  Node mapSkolem = getSkolem(n, inferInfo);
  Node countE = getMultiplicityTerm(e, mapSkolem);
  Node totalSum = d_nm->mkNode(APPLY_UF, sum, preImageSize);
  Node totalSumEqualCountE = d_nm->mkNode(EQUAL, totalSum, countE);

  // (forall ((i Int))
  //        (let ((uf_i (uf i)))
  //          (let ((count_uf_i (bag.count uf_i A)))
  //            (=>
  //             (and (>= i 1) (<= i preImageSize))
  //             (and
  //               (= (f uf_i) e)
  //               (>= count_uf_i 1)
  //               (= (sum i) (+ (sum (- i 1)) count_uf_i))
  //               (forall ((j Int))
  //                 (=>
  //                  (and (< i j) (<= j preImageSize))
  //                  (not (= (uf i) (uf j))))))
  //               )))))

  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node i = bvm->mkBoundVar<FirstIndexVarAttribute>(n, "i", d_nm->integerType());
  Node j =
      bvm->mkBoundVar<SecondIndexVarAttribute>(n, "j", d_nm->integerType());
  Node iList = d_nm->mkNode(BOUND_VAR_LIST, i);
  Node jList = d_nm->mkNode(BOUND_VAR_LIST, j);
  Node iPlusOne = d_nm->mkNode(ADD, i, d_one);
  Node iMinusOne = d_nm->mkNode(SUB, i, d_one);
  Node uf_i = d_nm->mkNode(APPLY_UF, uf, i);
  Node uf_j = d_nm->mkNode(APPLY_UF, uf, j);
  Node f_uf_i = d_nm->mkNode(APPLY_UF, f, uf_i);
  Node uf_iPlusOne = d_nm->mkNode(APPLY_UF, uf, iPlusOne);
  Node uf_iMinusOne = d_nm->mkNode(APPLY_UF, uf, iMinusOne);
  Node interval_i = d_nm->mkNode(
      AND, d_nm->mkNode(GEQ, i, d_one), d_nm->mkNode(LEQ, i, preImageSize));
  Node sum_i = d_nm->mkNode(APPLY_UF, sum, i);
  Node sum_iPlusOne = d_nm->mkNode(APPLY_UF, sum, iPlusOne);
  Node sum_iMinusOne = d_nm->mkNode(APPLY_UF, sum, iMinusOne);
  Node count_iMinusOne = d_nm->mkNode(BAG_COUNT, uf_iMinusOne, A);
  Node count_uf_i = d_nm->mkNode(BAG_COUNT, uf_i, A);
  Node inductiveCase =
      d_nm->mkNode(EQUAL, sum_i, d_nm->mkNode(ADD, sum_iMinusOne, count_uf_i));
  Node f_iEqualE = d_nm->mkNode(EQUAL, f_uf_i, e);
  Node geqOne = d_nm->mkNode(GEQ, count_uf_i, d_one);

  // i < j <= preImageSize
  Node interval_j = d_nm->mkNode(
      AND, d_nm->mkNode(LT, i, j), d_nm->mkNode(LEQ, j, preImageSize));
  // uf(i) != uf(j)
  Node uf_i_equals_uf_j = d_nm->mkNode(EQUAL, uf_i, uf_j);
  Node notEqual = d_nm->mkNode(EQUAL, uf_i, uf_j).negate();
  Node body_j = d_nm->mkNode(OR, interval_j.negate(), notEqual);
  Node forAll_j = quantifiers::BoundedIntegers::mkBoundedForall(jList, body_j);
  Node andNode =
      d_nm->mkNode(AND, {f_iEqualE, geqOne, inductiveCase, forAll_j});
  Node body_i = d_nm->mkNode(OR, interval_i.negate(), andNode);
  Node forAll_i = quantifiers::BoundedIntegers::mkBoundedForall(iList, body_i);
  Node preImageGTE_zero = d_nm->mkNode(GEQ, preImageSize, d_zero);
  Node conclusion = d_nm->mkNode(
      AND, {baseCase, totalSumEqualCountE, forAll_i, preImageGTE_zero});
  inferInfo.d_conclusion = conclusion;

  std::map<Node, Node> m;
  m[e] = conclusion;
  Trace("bags::InferenceGenerator::mapDown")
      << "conclusion: " << inferInfo.d_conclusion << std::endl;
  return std::tuple(inferInfo, uf, preImageSize);
}

InferInfo InferenceGenerator::mapUp(
    Node n, Node uf, Node preImageSize, Node y, Node x)
{
  Assert(n.getKind() == BAG_MAP && n[1].getType().isBag());
  Assert(n[0].getType().isFunction()
         && n[0].getType().getArgTypes().size() == 1);

  InferInfo inferInfo(d_im, InferenceId::BAGS_MAP_UP);
  Node f = n[0];
  Node A = n[1];

  Node countA = getMultiplicityTerm(x, A);
  Node xInA = d_nm->mkNode(GEQ, countA, d_one);
  Node notEqual = d_nm->mkNode(EQUAL, d_nm->mkNode(APPLY_UF, f, x), y).negate();

  Node k = d_sm->mkSkolemFunction(SkolemFunId::BAGS_MAP_PREIMAGE_INDEX,
                                  d_nm->integerType(),
                                  {n, uf, preImageSize, y, x});
  Node inRange = d_nm->mkNode(
      AND, d_nm->mkNode(GEQ, k, d_one), d_nm->mkNode(LEQ, k, preImageSize));
  Node equal = d_nm->mkNode(EQUAL, d_nm->mkNode(APPLY_UF, uf, k), x);
  Node andNode = d_nm->mkNode(AND, inRange, equal);
  Node orNode = d_nm->mkNode(OR, notEqual, andNode);
  Node implies = d_nm->mkNode(IMPLIES, xInA, orNode);
  inferInfo.d_conclusion = implies;
  Trace("bags::InferenceGenerator::mapUpwards")
      << "conclusion: " << inferInfo.d_conclusion << std::endl;
  return inferInfo;
}

InferInfo InferenceGenerator::filterDownwards(Node n, Node e)
{
  Assert(n.getKind() == BAG_FILTER && n[1].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[1].getType().getBagElementType()));

  Node P = n[0];
  Node A = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_FILTER_DOWN);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node member = d_nm->mkNode(GEQ, count, d_one);
  Node pOfe = d_nm->mkNode(APPLY_UF, P, e);
  Node equal = count.eqNode(countA);

  inferInfo.d_conclusion = pOfe.andNode(equal);
  inferInfo.d_premises.push_back(member);
  return inferInfo;
}

InferInfo InferenceGenerator::filterUpwards(Node n, Node e)
{
  Assert(n.getKind() == BAG_FILTER && n[1].getType().isBag());
  Assert(e.getType().isSubtypeOf(n[1].getType().getBagElementType()));

  Node P = n[0];
  Node A = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_FILTER_UP);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node member = d_nm->mkNode(GEQ, countA, d_one);
  Node pOfe = d_nm->mkNode(APPLY_UF, P, e);
  Node equal = count.eqNode(countA);
  Node included = pOfe.andNode(equal);
  Node equalZero = count.eqNode(d_zero);
  Node excluded = pOfe.notNode().andNode(equalZero);
  inferInfo.d_conclusion = included.orNode(excluded);
  inferInfo.d_premises.push_back(member);
  return inferInfo;
}

InferInfo InferenceGenerator::productUp(Node n, Node e1, Node e2)
{
  Assert(n.getKind() == TABLE_PRODUCT);
  Node A = n[0];
  Node B = n[1];
  Node tuple = BagsUtils::constructProductTuple(n, e1, e2);

  InferInfo inferInfo(d_im, InferenceId::TABLES_PRODUCT_UP);

  Node countA = getMultiplicityTerm(e1, A);
  Node countB = getMultiplicityTerm(e2, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(tuple, skolem);

  Node multiply = d_nm->mkNode(MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);

  return inferInfo;
}

InferInfo InferenceGenerator::productDown(Node n, Node e)
{
  Assert(n.getKind() == TABLE_PRODUCT);
  Assert(e.getType().isSubtypeOf(n.getType().getBagElementType()));

  Node A = n[0];
  Node B = n[1];

  TypeNode tupleBType = B.getType().getBagElementType();
  TypeNode tupleAType = A.getType().getBagElementType();
  size_t tupleALength = tupleAType.getTupleLength();
  size_t productTupleLength = n.getType().getBagElementType().getTupleLength();

  std::vector<Node> elements = TupleUtils::getTupleElements(e);
  Node a = TupleUtils::constructTupleFromElements(
      tupleAType, elements, 0, tupleALength - 1);
  Node b = TupleUtils::constructTupleFromElements(
      tupleBType, elements, tupleALength, productTupleLength - 1);

  InferInfo inferInfo(d_im, InferenceId::TABLES_PRODUCT_DOWN);

  Node countA = getMultiplicityTerm(a, A);
  Node countB = getMultiplicityTerm(b, B);

  Node skolem = getSkolem(n, inferInfo);
  Node count = getMultiplicityTerm(e, skolem);

  Node multiply = d_nm->mkNode(MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);

  return inferInfo;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
