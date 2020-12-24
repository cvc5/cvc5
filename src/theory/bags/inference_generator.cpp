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

#include "expr/skolem_manager.h"

namespace CVC4 {
namespace theory {
namespace bags {

InferenceGenerator::InferenceGenerator(NodeManager* nm) : d_nm(nm)
{
  d_sm = d_nm->getSkolemManager();
  d_true = d_nm->mkConst(true);
  d_zero = d_nm->mkConst(Rational(0));
  d_one = d_nm->mkConst(Rational(1));
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
  Node mA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  Node mB = d_nm->mkNode(kind::BAG_COUNT, e, B);
  Node equal = mA.eqNode(mB);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}
//
// struct BagsDeqIndexAttributeId
//{
//};
// typedef expr::Attribute<BagsDeqIndexAttributeId, Node> BagsDeqIndexAttribute;

InferInfo InferenceGenerator::bagDisequality(Node n)
{
  Assert(n.getKind() == kind::NOT && n[0].getKind() == kind::EQUAL);
  Assert(n[0][0].getType().isBag());

  Node A = n[0][0];
  Node B = n[0][1];

  TypeNode elementType = A.getType().getBagElementType();
  SkolemManager* sm = d_nm->getSkolemManager();
  Node pred;
  // Bound exists x => m(x)
  BoundVarManager* bvm = d_nm->getBoundVarManager();
  Node v;  // =  bvm->mkBoundVar<BagsDeqIndexAttribute>(n, elementType);

  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_DISEQUALITY;
  // add e as a new skolem variable
  inferInfo.d_new_skolem.push_back(v);
  inferInfo.d_premises.push_back(n);
  Node mA = d_nm->mkNode(kind::BAG_COUNT, v, A);
  Node mB = d_nm->mkNode(kind::BAG_COUNT, v, B);
  Node equal = mA.eqNode(mB);
  Node notEqual = equal.notNode();
  inferInfo.d_conclusion = notEqual;
  //  Node e = sm->mkSkolem(v, pred, "disequalityWitness", elementType);
  return inferInfo;
}

InferInfo InferenceGenerator::bagEmpty(Node e)
{
  EmptyBag emptyBag = EmptyBag(d_nm->mkBagType(e.getType()));
  Node empty = d_nm->mkConst(emptyBag);
  InferInfo inferInfo;
  inferInfo.d_id = Inference::BAG_EMPTY;
  Node multiplicity = d_nm->mkNode(kind::BAG_COUNT, e, empty);
  Node equal = multiplicity.eqNode(d_zero);
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
  Node countA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  Node countB = d_nm->mkNode(kind::BAG_COUNT, e, B);
  Node skolem = d_sm->mkPurifySkolem(n, "union_disjoint");
  inferInfo.d_new_skolem.push_back(skolem);
  Node countSkolem = d_nm->mkNode(kind::BAG_COUNT, e, skolem);
  Node sum = d_nm->mkNode(kind::PLUS, countA, countB);
  Node equal = countSkolem.eqNode(sum);
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
  Node mA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  Node mB = d_nm->mkNode(kind::BAG_COUNT, e, B);
  Node mUnionMax = d_nm->mkNode(kind::BAG_COUNT, e, n);
  Node gt = d_nm->mkNode(kind::GT, mA, mB);
  Node max = d_nm->mkNode(kind::ITE, gt, mA, mB);
  Node equal = mUnionMax.eqNode(max);
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
  Node mA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  Node mB = d_nm->mkNode(kind::BAG_COUNT, e, B);
  Node mIntersection = d_nm->mkNode(kind::BAG_COUNT, e, n);
  Node lt = d_nm->mkNode(kind::LT, mA, mB);
  Node min = d_nm->mkNode(kind::ITE, lt, mA, mB);
  Node equal = mIntersection.eqNode(min);
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
  Node mA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  Node mB = d_nm->mkNode(kind::BAG_COUNT, e, B);
  Node mDifference = d_nm->mkNode(kind::BAG_COUNT, e, n);
  Node subtract = d_nm->mkNode(kind::MINUS, mA, mB);
  Node gte = d_nm->mkNode(kind::GEQ, mA, mB);
  Node difference = d_nm->mkNode(kind::ITE, gte, subtract, d_zero);
  Node equal = mDifference.eqNode(difference);
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
  Node mA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  Node mB = d_nm->mkNode(kind::BAG_COUNT, e, B);
  Node mDifference = d_nm->mkNode(kind::BAG_COUNT, e, n);
  Node notInB = d_nm->mkNode(kind::EQUAL, mB, d_zero);
  Node difference = d_nm->mkNode(kind::ITE, notInB, mA, d_zero);
  Node equal = mDifference.eqNode(difference);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

InferInfo InferenceGenerator::duplicateRemoval(Node n, Node e)
{
  Assert(n.getKind() == kind::DUPLICATE_REMOVAL && n[0].getType().isBag());
  Assert(e.getType() == n[0].getType().getBagElementType());

  Node A = n[0];

  InferInfo inferInfo;
  Node mA = d_nm->mkNode(kind::BAG_COUNT, e, A);
  inferInfo.d_id = Inference::BAG_DUPLICATE_REMOVAL;

  Node multiplicity = d_nm->mkNode(kind::BAG_COUNT, e, A);

  Node mDistinct = d_nm->mkNode(kind::BAG_COUNT, e, n);
  Node gte = d_nm->mkNode(kind::GEQ, mA, d_one);
  Node ite = d_nm->mkNode(kind::ITE, gte, d_one, d_zero);
  Node equal = multiplicity.eqNode(ite);
  inferInfo.d_conclusion = equal;
  return inferInfo;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
