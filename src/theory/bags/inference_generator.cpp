/*********************                                                        */
/*! \file inference_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference generator utility
 **/

#include "inference_generator.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

InferenceGenerator::InferenceGenerator(SolverState* state) : d_state(state)
{
  d_nm = NodeManager::currentNM();
  d_sm = d_nm->getSkolemManager();
  d_true = d_nm->mkConst(true);
  d_zero = d_nm->mkConst(Rational(0));
  d_one = d_nm->mkConst(Rational(1));
}

InferInfo InferenceGenerator::mkBag(Node n, Node e)
{
  Assert(n.getKind() == kind::MK_BAG);
  Assert(e.getType() == n.getType().getBagElementType());

  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_MK_BAG;
  Node count = getMultiplicitySkolem(e, n, inferInfo);
  if (n[0] == e)
  {
    // TODO: refactor this with the rewriter
    // (=> true (= (bag.count e (bag e c)) c))
    inferInfo.d_conclusion = count.eqNode(n[1]);
  }
  else
  {
    // (=>
    //   true
    //   (= (bag.count e (bag x c)) (ite (= e x) c 0)))

    Node same = d_nm->mkNode(kind::EQUAL, n[0], e);
    Node ite = d_nm->mkNode(kind::ITE, same, n[1], d_zero);
    Node equal = count.eqNode(ite);
    inferInfo.d_conclusion = equal;
  }
  return inferInfo;
}

InferInfo InferenceGenerator::bagEquality(Node n, Node e)
{
  Assert(n.getKind() == kind::EQUAL && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];
  Node B = n[1];
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_EQUALITY;
  inferInfo.d_premises.push_back(n);
  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node countB = getMultiplicitySkolem(e, B, inferInfo);

  Node equal = countA.eqNode(countB);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

struct BagsDeqAttributeId
{
};
typedef expr::Attribute<BagsDeqAttributeId, Node> BagsDeqAttribute;

InferInfo InferenceGenerator::bagDisequality(Node n)
{
  Assert(n.getKind() == kind::NOT && n[0].getKind() == kind::EQUAL);
  Assert(n[0][0].getType().isBag());

  Node A = n[0][0];
  Node B = n[0][1];

  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_DISEQUALITY;

  TypeNode elementType = A.getType().getBagElementType();

  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node element = bvm->mkBoundVar<BagsDeqAttribute>(n, elementType);
  SkolemManager* sm = d_nm->getSkolemManager();
  Node skolem =
      sm->mkSkolem(element,
                   n,
                   "bag_disequal",
                   "an extensional lemma for disequality of two bags");

  inferInfo.d_newSkolem.push_back(skolem);

  Node countA = getMultiplicitySkolem(skolem, A, inferInfo);
  Node countB = getMultiplicitySkolem(skolem, B, inferInfo);

  Node disEqual = countA.eqNode(countB).notNode();

  inferInfo.d_premises.push_back(n);
  inferInfo.d_conclusion = disEqual;
  return inferInfo;
}

InferInfo InferenceGenerator::bagEmpty(Node e)
{
  EmptyBag emptyBag = EmptyBag(d_nm->mkBagType(e.getType()));
  Node empty = d_nm->mkConst(emptyBag);
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_EMPTY;
  Node count = getMultiplicitySkolem(e, empty, inferInfo);

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
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_UNION_DISJOINT;

  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node countB = getMultiplicitySkolem(e, B, inferInfo);
  Node count = getMultiplicitySkolem(e, n, inferInfo);

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
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_UNION_MAX;

  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node countB = getMultiplicitySkolem(e, B, inferInfo);
  Node count = getMultiplicitySkolem(e, n, inferInfo);

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
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_INTERSECTION_MIN;

  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node countB = getMultiplicitySkolem(e, B, inferInfo);
  Node count = getMultiplicitySkolem(e, n, inferInfo);

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
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_DIFFERENCE_SUBTRACT;

  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node countB = getMultiplicitySkolem(e, B, inferInfo);
  Node count = getMultiplicitySkolem(e, n, inferInfo);

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
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_DIFFERENCE_REMOVE;

  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node countB = getMultiplicitySkolem(e, B, inferInfo);
  Node count = getMultiplicitySkolem(e, n, inferInfo);

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
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_DUPLICATE_REMOVAL;

  Node countA = getMultiplicitySkolem(e, A, inferInfo);
  Node count = getMultiplicitySkolem(e, n, inferInfo);

  Node gte = d_nm->mkNode(kind::GEQ, countA, d_one);
  Node ite = d_nm->mkNode(kind::ITE, gte, d_one, d_zero);
  Node equal = count.eqNode(ite);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

Node InferenceGenerator::getMultiplicitySkolem(Node element,
                                               Node bag,
                                               InferInfo& inferInfo)
{
  Node count = d_nm->mkNode(kind::BAG_COUNT, element, bag);
  Node skolem = d_state->registerBagElement(count);
  eq::EqualityEngine* ee = d_state->getEqualityEngine();
  ee->assertEquality(skolem.eqNode(count), true, d_nm->mkConst(true));
  inferInfo.d_newSkolem.push_back(skolem);
  return skolem;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
