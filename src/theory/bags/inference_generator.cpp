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
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/uf/equality_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;

namespace cvc5::internal {
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

void InferenceGenerator::registerCountTerm(Node n)
{
  Assert(n.getKind() == BAG_COUNT);
  Node element = d_state->getRepresentative(n[0]);
  Node bag = d_state->getRepresentative(n[1]);
  Node count = d_nm->mkNode(BAG_COUNT, element, bag);
  Node skolem = registerAndAssertSkolemLemma(count);
  d_state->registerCountTerm(bag, element, skolem);
}

void InferenceGenerator::registerCardinalityTerm(Node n)
{
  Assert(n.getKind() == BAG_CARD);
  Node bag = d_state->getRepresentative(n[0]);
  Node cardTerm = d_nm->mkNode(BAG_CARD, bag);
  Node skolem = registerAndAssertSkolemLemma(cardTerm);
  d_state->registerCardinalityTerm(cardTerm, skolem);
  Node premise = n[0].eqNode(bag);
  Node conclusion = skolem.eqNode(n);
  Node lemma = premise.notNode().orNode(conclusion);
  d_im->addPendingLemma(lemma, InferenceId::BAGS_SKOLEM);
}

InferInfo InferenceGenerator::nonNegativeCount(Node n, Node e)
{
  Assert(n.getType().isBag());
  Assert(e.getType() == n.getType().getBagElementType());

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
  Assert(e.getType() == n.getType().getBagElementType());

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
  Node skolem = registerAndAssertSkolemLemma(n);
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

InferInfo InferenceGenerator::bagDisequality(Node equality, Node witness)
{
  Assert(equality.getKind() == EQUAL && equality[0].getType().isBag());
  Node A = equality[0];
  Node B = equality[1];

  InferInfo inferInfo(d_im, InferenceId::BAGS_DISEQUALITY);

  Node countA = getMultiplicityTerm(witness, A);
  Node countB = getMultiplicityTerm(witness, B);

  Node disequal = countA.eqNode(countB).notNode();

  inferInfo.d_premises.push_back(equality.notNode());
  inferInfo.d_conclusion = disequal;
  return inferInfo;
}

Node InferenceGenerator::registerAndAssertSkolemLemma(Node& n)
{
  Node skolem = d_sm->mkPurifySkolem(n);
  Node lemma = n.eqNode(skolem);
  d_im->addPendingLemma(lemma, InferenceId::BAGS_SKOLEM);
  Trace("bags-skolems") << "bags-skolems:  " << skolem << " = " << n
                        << std::endl;
  return skolem;
}

InferInfo InferenceGenerator::empty(Node n, Node e)
{
  Assert(n.getKind() == BAG_EMPTY);
  Assert(e.getType() == n.getType().getBagElementType());

  InferInfo inferInfo(d_im, InferenceId::BAGS_EMPTY);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node equal = count.eqNode(d_zero);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionDisjoint(Node n, Node e)
{
  Assert(n.getKind() == BAG_UNION_DISJOINT && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_DISJOINT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node sum = d_nm->mkNode(ADD, countA, countB);
  Node equal = count.eqNode(sum);

  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::unionMax(Node n, Node e)
{
  Assert(n.getKind() == BAG_UNION_MAX && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_UNION_MAX);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = registerAndAssertSkolemLemma(n);
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
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_INTERSECTION_MIN);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = registerAndAssertSkolemLemma(n);
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
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_SUBTRACT);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);
  Node skolem = registerAndAssertSkolemLemma(n);
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
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DIFFERENCE_REMOVE);

  Node countA = getMultiplicityTerm(e, A);
  Node countB = getMultiplicityTerm(e, B);

  Node skolem = registerAndAssertSkolemLemma(n);
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
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  InferInfo inferInfo(d_im, InferenceId::BAGS_DUPLICATE_REMOVAL);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = registerAndAssertSkolemLemma(n);
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
  InferInfo inferInfo(d_im, InferenceId::BAGS_CARD_EMPTY);
  Node premise = pair.first[0].eqNode(n);
  Node conclusion = pair.second.eqNode(d_zero);
  inferInfo.d_conclusion = premise.eqNode(conclusion);
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
  Node sum = registerAndAssertSkolemLemma(card);
  ++it;
  while (it != children.end())
  {
    child = *it;
    d_state->registerBag(child);
    unionDisjoints =
        d_nm->mkNode(kind::BAG_UNION_DISJOINT, unionDisjoints, child);
    card = d_nm->mkNode(BAG_CARD, child);
    Node skolem = registerAndAssertSkolemLemma(card);
    sum = d_nm->mkNode(ADD, sum, skolem);
    ++it;
  }
  Node parentCard = d_nm->mkNode(BAG_CARD, parent);
  Node parentSkolem = registerAndAssertSkolemLemma(parentCard);

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
  Node preImageSize = d_sm->mkSkolemFunction(
      SkolemFunId::BAGS_MAP_PREIMAGE_SIZE, d_nm->integerType(), {n, e});

  // (= (sum preImageSize) (bag.count e skolem))
  Node mapSkolem = registerAndAssertSkolemLemma(n);
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

InferInfo InferenceGenerator::filterDown(Node n, Node e)
{
  Assert(n.getKind() == BAG_FILTER && n[1].getType().isBag());
  Assert(e.getType() == n[1].getType().getBagElementType());

  Node P = n[0];
  Node A = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_FILTER_DOWN);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);

  Node member = d_nm->mkNode(GEQ, count, d_one);
  Node pOfe = d_nm->mkNode(APPLY_UF, P, e);
  Node equal = count.eqNode(countA);

  inferInfo.d_conclusion = pOfe.andNode(equal);
  inferInfo.d_premises.push_back(member);
  return inferInfo;
}

InferInfo InferenceGenerator::filterUp(Node n, Node e)
{
  Assert(n.getKind() == BAG_FILTER && n[1].getType().isBag());
  Assert(e.getType() == n[1].getType().getBagElementType());

  Node P = n[0];
  Node A = n[1];
  InferInfo inferInfo(d_im, InferenceId::BAGS_FILTER_UP);

  Node countA = getMultiplicityTerm(e, A);
  Node skolem = registerAndAssertSkolemLemma(n);
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

  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, countA, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, countB, d_one));

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(tuple, skolem);

  Node multiply = d_nm->mkNode(MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);

  return inferInfo;
}

InferInfo InferenceGenerator::productDown(Node n, Node e)
{
  Assert(n.getKind() == TABLE_PRODUCT);
  Assert(e.getType() == n.getType().getBagElementType());

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

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count, d_one));

  Node multiply = d_nm->mkNode(MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);

  return inferInfo;
}

InferInfo InferenceGenerator::joinUp(Node n, Node e1, Node e2)
{
  Assert(n.getKind() == TABLE_JOIN);
  Node A = n[0];
  Node B = n[1];
  Node tuple = BagsUtils::constructProductTuple(n, e1, e2);

  std::vector<Node> aElements = TupleUtils::getTupleElements(e1);
  std::vector<Node> bElements = TupleUtils::getTupleElements(e2);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  InferInfo inferInfo(d_im, InferenceId::TABLES_PRODUCT_UP);

  for (size_t i = 0; i < indices.size(); i += 2)
  {
    Node x = aElements[indices[i]];
    Node y = bElements[indices[i + 1]];
    Node equal = x.eqNode(y);
    inferInfo.d_premises.push_back(equal);
  }

  Node countA = getMultiplicityTerm(e1, A);
  Node countB = getMultiplicityTerm(e2, B);

  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, countA, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, countB, d_one));

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(tuple, skolem);

  Node multiply = d_nm->mkNode(MULT, countA, countB);
  inferInfo.d_conclusion = count.eqNode(multiply);
  return inferInfo;
}

InferInfo InferenceGenerator::joinDown(Node n, Node e)
{
  Assert(n.getKind() == TABLE_JOIN);
  Assert(e.getType() == n.getType().getBagElementType());

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

  InferInfo inferInfo(d_im, InferenceId::TABLES_JOIN_DOWN);

  Node countA = getMultiplicityTerm(a, A);
  Node countB = getMultiplicityTerm(b, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count = getMultiplicityTerm(e, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count, d_one));

  Node multiply = d_nm->mkNode(MULT, countA, countB);
  Node multiplicityConstraint = count.eqNode(multiply);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();
  Node joinConstraints = d_true;
  for (size_t i = 0; i < indices.size(); i += 2)
  {
    Node x = elements[indices[i]];
    Node y = elements[tupleALength + indices[i + 1]];
    Node equal = x.eqNode(y);
    joinConstraints = joinConstraints.andNode(equal);
  }
  inferInfo.d_conclusion = joinConstraints.andNode(multiplicityConstraint);

  return inferInfo;
}

InferInfo InferenceGenerator::groupNotEmpty(Node n)
{
  Assert(n.getKind() == TABLE_GROUP);

  TypeNode bagType = n.getType();
  Node A = n[0];
  Node emptyPart = d_nm->mkConst(EmptyBag(A.getType()));
  Node skolem = registerAndAssertSkolemLemma(n);
  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_NOT_EMPTY);
  Node A_isEmpty = A.eqNode(emptyPart);
  inferInfo.d_premises.push_back(A_isEmpty);
  Node singleton = d_nm->mkNode(BAG_MAKE, emptyPart, d_one);
  Node groupIsSingleton = skolem.eqNode(singleton);

  inferInfo.d_conclusion = groupIsSingleton;
  return inferInfo;
}

InferInfo InferenceGenerator::groupUp1(Node n, Node x, Node part)
{
  Assert(n.getKind() == TABLE_GROUP);
  Assert(x.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_UP1);
  Node count_x_A = getMultiplicityTerm(x, A);
  Node x_member_A = d_nm->mkNode(GEQ, count_x_A, d_one);
  inferInfo.d_premises.push_back(x_member_A);

  Node part_x = d_nm->mkNode(APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);

  Node count_x_part_x = getMultiplicityTerm(x, part_x);

  Node sameMultiplicity = count_x_part_x.eqNode(count_x_A);
  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_part_x = getMultiplicityTerm(part_x, skolem);
  Node part_x_member = d_nm->mkNode(EQUAL, count_part_x, d_one);

  Node emptyPart = d_nm->mkConst(EmptyBag(bagType));
  Node count_emptyPart = getMultiplicityTerm(emptyPart, skolem);
  Node emptyPart_not_member = count_emptyPart.eqNode(d_zero);

  inferInfo.d_conclusion = d_nm->mkNode(
      AND, {sameMultiplicity, part_x_member, emptyPart_not_member});
  return inferInfo;
}

InferInfo InferenceGenerator::groupUp2(Node n, Node x, Node part)
{
  Assert(n.getKind() == TABLE_GROUP);
  Assert(x.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_UP2);
  Node count_x_A = getMultiplicityTerm(x, A);
  Node x_not_in_A = d_nm->mkNode(EQUAL, count_x_A, d_zero);
  inferInfo.d_premises.push_back(x_not_in_A);

  Node part_x = d_nm->mkNode(APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_x_is_empty = part_x.eqNode(d_nm->mkConst(EmptyBag(bagType)));
  inferInfo.d_conclusion = part_x_is_empty;
  return inferInfo;
}

InferInfo InferenceGenerator::groupDown(Node n, Node B, Node x, Node part)
{
  Assert(n.getKind() == TABLE_GROUP);
  Assert(B.getType() == n.getType().getBagElementType());
  Assert(x.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_DOWN);
  Node count_x_B = getMultiplicityTerm(x, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_B_n, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_x_B, d_one));
  Node count_x_A = getMultiplicityTerm(x, A);
  Node sameMultiplicity = count_x_B.eqNode(count_x_A);
  Node part_x = d_nm->mkNode(APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_x_is_B = part_x.eqNode(B);
  inferInfo.d_conclusion = d_nm->mkNode(AND, sameMultiplicity, part_x_is_B);
  return inferInfo;
}

InferInfo InferenceGenerator::groupPartCount(Node n, Node B, Node part)
{
  Assert(n.getKind() == TABLE_GROUP);
  Assert(B.getType() == n.getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();
  Node empty = d_nm->mkConst(EmptyBag(bagType));

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_PART_COUNT);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_B_n, d_one));
  Node A_notEmpty = A.eqNode(empty).notNode();
  inferInfo.d_premises.push_back(A_notEmpty);

  Node x = d_sm->mkSkolemFunction(SkolemFunId::TABLES_GROUP_PART_ELEMENT,
                                  bagType.getBagElementType(),
                                  {n, B});
  d_state->registerPartElementSkolem(n, x);
  Node part_x = d_nm->mkNode(APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node B_is_part_x = B.eqNode(part_x);
  Node count_x_A = getMultiplicityTerm(x, A);
  Node count_x_B = getMultiplicityTerm(x, B);
  Node sameMultiplicity = count_x_A.eqNode(count_x_B);
  Node x_in_B = d_nm->mkNode(GEQ, count_x_B, d_one);
  Node count_B_n_is_one = count_B_n.eqNode(d_one);
  inferInfo.d_conclusion = d_nm->mkNode(AND,
                                        {
                                            count_B_n_is_one,
                                            B_is_part_x,
                                            x_in_B,
                                            sameMultiplicity,
                                        });
  return inferInfo;
}

InferInfo InferenceGenerator::groupSameProjection(
    Node n, Node B, Node x, Node y, Node part)
{
  Assert(n.getKind() == TABLE_GROUP);
  Assert(B.getType() == n.getType().getBagElementType());
  Assert(x.getType() == n[0].getType().getBagElementType());
  Assert(y.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_SAME_PROJECTION);
  Node count_x_B = getMultiplicityTerm(x, B);
  Node count_y_B = getMultiplicityTerm(y, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);

  // premises
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_B_n, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_x_B, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_y_B, d_one));
  inferInfo.d_premises.push_back(x.eqNode(y).notNode());

  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  Node xProjection = TupleUtils::getTupleProjection(indices, x);
  Node yProjection = TupleUtils::getTupleProjection(indices, y);
  Node sameProjection = xProjection.eqNode(yProjection);
  Node part_x = d_nm->mkNode(APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_y = d_nm->mkNode(APPLY_UF, part, y);
  part_y = registerAndAssertSkolemLemma(part_y);
  Node samePart = part_x.eqNode(part_y);
  Node part_x_is_B = part_x.eqNode(B);
  inferInfo.d_conclusion =
      d_nm->mkNode(AND, sameProjection, samePart, part_x_is_B);
  return inferInfo;
}

InferInfo InferenceGenerator::groupSamePart(
    Node n, Node B, Node x, Node y, Node part)
{
  Assert(n.getKind() == TABLE_GROUP);
  Assert(B.getType() == n.getType().getBagElementType());
  Assert(x.getType() == n[0].getType().getBagElementType());
  Assert(y.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  TypeNode bagType = A.getType();

  InferInfo inferInfo(d_im, InferenceId::TABLES_GROUP_SAME_PART);
  Node count_x_B = getMultiplicityTerm(x, B);
  Node count_y_A = getMultiplicityTerm(y, A);
  Node count_y_B = getMultiplicityTerm(y, B);

  Node skolem = registerAndAssertSkolemLemma(n);
  Node count_B_n = getMultiplicityTerm(B, skolem);
  const std::vector<uint32_t>& indices =
      n.getOperator().getConst<ProjectOp>().getIndices();

  Node xProjection = TupleUtils::getTupleProjection(indices, x);
  Node yProjection = TupleUtils::getTupleProjection(indices, y);

  // premises
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_B_n, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_x_B, d_one));
  inferInfo.d_premises.push_back(d_nm->mkNode(GEQ, count_y_A, d_one));
  inferInfo.d_premises.push_back(x.eqNode(y).notNode());
  inferInfo.d_premises.push_back(xProjection.eqNode(yProjection));

  Node sameMultiplicity = count_y_B.eqNode(count_y_A);
  Node part_x = d_nm->mkNode(APPLY_UF, part, x);
  part_x = registerAndAssertSkolemLemma(part_x);
  Node part_y = d_nm->mkNode(APPLY_UF, part, y);
  part_y = registerAndAssertSkolemLemma(part_y);
  Node samePart = part_x.eqNode(part_y);
  Node part_x_is_B = part_x.eqNode(B);
  inferInfo.d_conclusion =
      d_nm->mkNode(AND, sameMultiplicity, samePart, part_x_is_B);

  return inferInfo;
}

Node InferenceGenerator::defineSkolemPartFunction(Node n)
{
  Assert(n.getKind() == TABLE_GROUP);
  Node A = n[0];
  TypeNode tableType = A.getType();
  TypeNode elementType = tableType.getBagElementType();

  // declare an uninterpreted function part: T -> (Table T)
  TypeNode partType = d_nm->mkFunctionType(elementType, tableType);
  Node part =
      d_sm->mkSkolemFunction(SkolemFunId::TABLES_GROUP_PART, partType, {n});
  return part;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
