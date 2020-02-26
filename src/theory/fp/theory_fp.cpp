/*********************                                                        */
/*! \file theory_fp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "options/fp_options.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "theory/fp/theory_fp.h"


#include <set>
#include <stack>
#include <unordered_set>
#include <vector>

using namespace std;

namespace CVC4 {
namespace theory {
namespace fp {

namespace removeToFPGeneric {

Node removeToFPGeneric(TNode node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC);

  FloatingPointToFPGeneric info =
      node.getOperator().getConst<FloatingPointToFPGeneric>();

  size_t children = node.getNumChildren();

  Node op;
  NodeManager *nm = NodeManager::currentNM();

  if (children == 1) {
    op = nm->mkConst(FloatingPointToFPIEEEBitVector(info));
    return nm->mkNode(op, node[0]);

  } else {
    Assert(children == 2);
    Assert(node[0].getType().isRoundingMode());

    TypeNode t = node[1].getType();

    if (t.isFloatingPoint()) {
      op = nm->mkConst(FloatingPointToFPFloatingPoint(info));
    } else if (t.isReal()) {
      op = nm->mkConst(FloatingPointToFPReal(info));
    } else if (t.isBitVector()) {
      op = nm->mkConst(FloatingPointToFPSignedBitVector(info));
    } else {
      throw TypeCheckingExceptionPrivate(
          node,
          "cannot rewrite to_fp generic due to incorrect type of second "
          "argument");
    }

    return nm->mkNode(op, node[0], node[1]);
  }

  Unreachable() << "to_fp generic not rewritten";
}
}  // namespace removeToFPGeneric

namespace helper {
Node buildConjunct(const std::vector<TNode> &assumptions) {
  if (assumptions.size() == 0) {
    return NodeManager::currentNM()->mkConst<bool>(true);

  } else if (assumptions.size() == 1) {
    return assumptions[0];

  } else {
    // \todo see bv::utils::flattenAnd

    NodeBuilder<> conjunction(kind::AND);
    for (std::vector<TNode>::const_iterator it = assumptions.begin();
         it != assumptions.end(); ++it) {
      conjunction << *it;
    }

    return conjunction;
  }
}
}  // namespace helper

/** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
TheoryFp::TheoryFp(context::Context *c,
                   context::UserContext *u,
                   OutputChannel &out,
                   Valuation valuation,
                   const LogicInfo &logicInfo)
    : Theory(THEORY_FP, c, u, out, valuation, logicInfo),
      d_notification(*this),
      d_equalityEngine(d_notification, c, "theory::fp::ee", true),
      d_registeredTerms(u),
      d_conv(u),
      d_expansionRequested(false),
      d_conflict(c, false),
      d_conflictNode(c, Node::null()),
      d_minMap(u),
      d_maxMap(u),
      d_toUBVMap(u),
      d_toSBVMap(u),
      d_toRealMap(u),
      realToFloatMap(u),
      floatToRealMap(u),
      abstractionMap(u)
{
  // Kinds that are to be handled in the congruence closure

  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ABS);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_NEG);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_PLUS);
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_SUB); // Removed
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MULT);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_DIV);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_FMA);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_SQRT);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_REM);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_RTI);
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MIN); // Removed
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MAX); // Removed
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MIN_TOTAL);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_MAX_TOTAL);

  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_EQ); // Removed
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_LEQ);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_LT);
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_GEQ); // Removed
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_GT); // Removed
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISN);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISSN);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISZ);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISINF);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISNAN);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISNEG);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_ISPOS);

  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_REAL);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR);
  d_equalityEngine.addFunctionKind(
      kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR);
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_FP_GENERIC); //
  // Needed in parsing, should be rewritten away

  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_UBV); // Removed
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_SBV); // Removed
  // d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_REAL); // Removed
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_UBV_TOTAL);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_SBV_TOTAL);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_TO_REAL_TOTAL);

  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_NAN);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_INF);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_ZERO);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGN);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_EXPONENT);
  d_equalityEngine.addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);
  d_equalityEngine.addFunctionKind(kind::ROUNDINGMODE_BITBLAST);

} /* TheoryFp::TheoryFp() */

Node TheoryFp::minUF(Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_MIN);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  ComparisonUFMap::const_iterator i(d_minMap.find(t));

  Node fun;
  if (i == d_minMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = t;
    fun = nm->mkSkolem("floatingpoint_min_zero_case",
                       nm->mkFunctionType(args,
#ifdef SYMFPUPROPISBOOL
                                          nm->booleanType()
#else
                                          nm->mkBitVectorType(1U)
#endif
                                              ),
                       "floatingpoint_min_zero_case",
                       NodeManager::SKOLEM_EXACT_NAME);
    d_minMap.insert(t, fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[1],
                    node[0]);  // Application reverses the order or arguments
}

Node TheoryFp::maxUF(Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_MAX);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  ComparisonUFMap::const_iterator i(d_maxMap.find(t));

  Node fun;
  if (i == d_maxMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = t;
    fun = nm->mkSkolem("floatingpoint_max_zero_case",
                       nm->mkFunctionType(args,
#ifdef SYMFPUPROPISBOOL
                                          nm->booleanType()
#else
                                          nm->mkBitVectorType(1U)
#endif
                                              ),
                       "floatingpoint_max_zero_case",
                       NodeManager::SKOLEM_EXACT_NAME);
    d_maxMap.insert(t, fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[1], node[0]);
}

Node TheoryFp::toUBVUF(Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV);

  TypeNode target(node.getType());
  Assert(target.getKind() == kind::BITVECTOR_TYPE);

  TypeNode source(node[1].getType());
  Assert(source.getKind() == kind::FLOATINGPOINT_TYPE);

  std::pair<TypeNode, TypeNode> p(source, target);
  NodeManager *nm = NodeManager::currentNM();
  ConversionUFMap::const_iterator i(d_toUBVMap.find(p));

  Node fun;
  if (i == d_toUBVMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = nm->roundingModeType();
    args[1] = source;
    fun = nm->mkSkolem("floatingpoint_to_ubv_out_of_range_case",
                       nm->mkFunctionType(args, target),
                       "floatingpoint_to_ubv_out_of_range_case",
                       NodeManager::SKOLEM_EXACT_NAME);
    d_toUBVMap.insert(p, fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);
}

Node TheoryFp::toSBVUF(Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV);

  TypeNode target(node.getType());
  Assert(target.getKind() == kind::BITVECTOR_TYPE);

  TypeNode source(node[1].getType());
  Assert(source.getKind() == kind::FLOATINGPOINT_TYPE);

  std::pair<TypeNode, TypeNode> p(source, target);
  NodeManager *nm = NodeManager::currentNM();
  ConversionUFMap::const_iterator i(d_toSBVMap.find(p));

  Node fun;
  if (i == d_toSBVMap.end()) {
    std::vector<TypeNode> args(2);
    args[0] = nm->roundingModeType();
    args[1] = source;
    fun = nm->mkSkolem("floatingpoint_to_sbv_out_of_range_case",
                       nm->mkFunctionType(args, target),
                       "floatingpoint_to_sbv_out_of_range_case",
                       NodeManager::SKOLEM_EXACT_NAME);
    d_toSBVMap.insert(p, fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);
}

Node TheoryFp::toRealUF(Node node) {
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL);
  TypeNode t(node[0].getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  ComparisonUFMap::const_iterator i(d_toRealMap.find(t));

  Node fun;
  if (i == d_toRealMap.end()) {
    std::vector<TypeNode> args(1);
    args[0] = t;
    fun = nm->mkSkolem("floatingpoint_to_real_infinity_and_NaN_case",
                       nm->mkFunctionType(args, nm->realType()),
                       "floatingpoint_to_real_infinity_and_NaN_case",
                       NodeManager::SKOLEM_EXACT_NAME);
    d_toRealMap.insert(t, fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0]);
}

void TheoryFp::enableUF(LogicRequest &lr)
{
  if (!this->d_expansionRequested) {
    // Needed for conversions to/from real and min/max
    lr.widenLogic(THEORY_UF);
    // THEORY_BV has to be enabled when the logic is set
    this->d_expansionRequested = true;
  }
  return;
}

Node TheoryFp::abstractRealToFloat(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_REAL);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  ComparisonUFMap::const_iterator i(realToFloatMap.find(t));

  Node fun;
  if (i == realToFloatMap.end())
  {
    std::vector<TypeNode> args(2);
    args[0] = node[0].getType();
    args[1] = node[1].getType();
    fun = nm->mkSkolem("floatingpoint_abstract_real_to_float",
                       nm->mkFunctionType(args, node.getType()),
                       "floatingpoint_abstract_real_to_float",
                       NodeManager::SKOLEM_EXACT_NAME);
    realToFloatMap.insert(t, fun);
  }
  else
  {
    fun = (*i).second;
  }
  Node uf = nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);

  abstractionMap.insert(uf, node);

  return uf;
}

Node TheoryFp::abstractFloatToReal(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL);
  TypeNode t(node[0].getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager *nm = NodeManager::currentNM();
  ComparisonUFMap::const_iterator i(floatToRealMap.find(t));

  Node fun;
  if (i == floatToRealMap.end())
  {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = nm->realType();
    fun = nm->mkSkolem("floatingpoint_abstract_float_to_real",
                       nm->mkFunctionType(args, nm->realType()),
                       "floatingpoint_abstract_float_to_real",
                       NodeManager::SKOLEM_EXACT_NAME);
    floatToRealMap.insert(t, fun);
  }
  else
  {
    fun = (*i).second;
  }
  Node uf = nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);

  abstractionMap.insert(uf, node);

  return uf;
}

Node TheoryFp::expandDefinition(LogicRequest &lr, Node node)
{
  Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node
                               << std::endl;

  Node res = node;

  if (node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC) {
    res = removeToFPGeneric::removeToFPGeneric(node);

  } else if (node.getKind() == kind::FLOATINGPOINT_MIN) {
    enableUF(lr);
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_MIN_TOTAL,
                                           node[0], node[1], minUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_MAX) {
    enableUF(lr);
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_MAX_TOTAL,
                                           node[0], node[1], maxUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_UBV) {
    enableUF(lr);
    FloatingPointToUBV info = node.getOperator().getConst<FloatingPointToUBV>();
    FloatingPointToUBVTotal newInfo(info);

    res =
        NodeManager::currentNM()->mkNode(  // kind::FLOATINGPOINT_TO_UBV_TOTAL,
            NodeManager::currentNM()->mkConst(newInfo), node[0], node[1],
            toUBVUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_SBV) {
    enableUF(lr);
    FloatingPointToSBV info = node.getOperator().getConst<FloatingPointToSBV>();
    FloatingPointToSBVTotal newInfo(info);

    res =
        NodeManager::currentNM()->mkNode(  // kind::FLOATINGPOINT_TO_SBV_TOTAL,
            NodeManager::currentNM()->mkConst(newInfo), node[0], node[1],
            toSBVUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_REAL) {
    enableUF(lr);
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
                                           node[0], toRealUF(node));

  } else {
    // Do nothing
  }

  // We will need to enable UF to abstract these in ppRewrite
  if (res.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL
      || res.getKind() == kind::FLOATINGPOINT_TO_FP_REAL)
  {
    enableUF(lr);
  }

  if (res != node) {
    Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node
                                 << " rewritten to " << res << std::endl;
  }

  return res;
}

Node TheoryFp::ppRewrite(TNode node)
{
  Trace("fp-ppRewrite") << "TheoryFp::ppRewrite(): " << node << std::endl;

  Node res = node;

  // Abstract conversion functions
  if (node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL)
  {
    res = abstractFloatToReal(node);

    // Generate some lemmas
    NodeManager *nm = NodeManager::currentNM();

    Node pd =
        nm->mkNode(kind::IMPLIES,
                   nm->mkNode(kind::OR,
                              nm->mkNode(kind::FLOATINGPOINT_ISNAN, node[0]),
                              nm->mkNode(kind::FLOATINGPOINT_ISINF, node[0])),
                   nm->mkNode(kind::EQUAL, res, node[1]));
    handleLemma(pd);

    Node z =
        nm->mkNode(kind::IMPLIES,
                   nm->mkNode(kind::FLOATINGPOINT_ISZ, node[0]),
                   nm->mkNode(kind::EQUAL, res, nm->mkConst(Rational(0U))));
    handleLemma(z);

    // TODO : bounds on the output from largest floats, #1914
  }
  else if (node.getKind() == kind::FLOATINGPOINT_TO_FP_REAL)
  {
    res = abstractRealToFloat(node);

    // Generate some lemmas
    NodeManager *nm = NodeManager::currentNM();

    Node nnan =
        nm->mkNode(kind::NOT, nm->mkNode(kind::FLOATINGPOINT_ISNAN, res));
    handleLemma(nnan);

    Node z = nm->mkNode(
        kind::IMPLIES,
        nm->mkNode(kind::EQUAL, node[1], nm->mkConst(Rational(0U))),
        nm->mkNode(kind::EQUAL,
                   res,
                   nm->mkConst(FloatingPoint::makeZero(
                       res.getType().getConst<FloatingPointSize>(), false))));
    handleLemma(z);

    // TODO : rounding-mode specific bounds on floats that don't give infinity
    // BEWARE of directed rounding!   #1914
  }

  if (res != node)
  {
    Trace("fp-ppRewrite") << "TheoryFp::ppRewrite(): node " << node
                          << " rewritten to " << res << std::endl;
  }

  return res;
}

bool TheoryFp::refineAbstraction(TheoryModel *m, TNode abstract, TNode concrete)
{
  Trace("fp-refineAbstraction") << "TheoryFp::refineAbstraction(): " << abstract
                                << " vs. " << concrete << std::endl;
  Kind k = concrete.getKind();
  if (k == kind::FLOATINGPOINT_TO_REAL_TOTAL)
  {
    // Get the values
    Assert(m->hasTerm(abstract));
    Assert(m->hasTerm(concrete[0]));
    Assert(m->hasTerm(concrete[1]));

    Node abstractValue = m->getValue(abstract);
    Node floatValue = m->getValue(concrete[0]);
    Node undefValue = m->getValue(concrete[1]);

    Assert(abstractValue.isConst());
    Assert(floatValue.isConst());
    Assert(undefValue.isConst());

    // Work out the actual value for those args
    NodeManager *nm = NodeManager::currentNM();

    Node evaluate =
        nm->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL, floatValue, undefValue);
    Node concreteValue = Rewriter::rewrite(evaluate);
    Assert(concreteValue.isConst());

    Trace("fp-refineAbstraction")
        << "TheoryFp::refineAbstraction(): " << concrete[0] << " = "
        << floatValue << std::endl
        << "TheoryFp::refineAbstraction(): " << concrete[1] << " = "
        << undefValue << std::endl
        << "TheoryFp::refineAbstraction(): " << abstract << " = "
        << abstractValue << std::endl
        << "TheoryFp::refineAbstraction(): " << concrete << " = "
        << concreteValue << std::endl;

    if (abstractValue != concreteValue)
    {
      // Need refinement lemmas
      // only in the normal and subnormal case
      Assert(floatValue.getConst<FloatingPoint>().isNormal()
             || floatValue.getConst<FloatingPoint>().isSubnormal());

      Node defined = nm->mkNode(
          kind::AND,
          nm->mkNode(kind::NOT,
                     nm->mkNode(kind::FLOATINGPOINT_ISNAN, concrete[0])),
          nm->mkNode(kind::NOT,
                     nm->mkNode(kind::FLOATINGPOINT_ISINF, concrete[0])));
      // First the "forward" constraints
      Node fg = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(kind::FLOATINGPOINT_GEQ, concrete[0], floatValue),
              nm->mkNode(kind::GEQ, abstract, concreteValue)));
      handleLemma(fg);

      Node fl = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(kind::FLOATINGPOINT_LEQ, concrete[0], floatValue),
              nm->mkNode(kind::LEQ, abstract, concreteValue)));
      handleLemma(fl);

      // Then the backwards constraints
      Node floatAboveAbstract = Rewriter::rewrite(
          nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
                     nm->mkConst(FloatingPointToFPReal(
                         concrete[0].getType().getConst<FloatingPointSize>())),
                     nm->mkConst(roundTowardPositive),
                     abstractValue));

      Node bg = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(
                  kind::FLOATINGPOINT_GEQ, concrete[0], floatAboveAbstract),
              nm->mkNode(kind::GEQ, abstract, abstractValue)));
      handleLemma(bg);

      Node floatBelowAbstract = Rewriter::rewrite(
          nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
                     nm->mkConst(FloatingPointToFPReal(
                         concrete[0].getType().getConst<FloatingPointSize>())),
                     nm->mkConst(roundTowardNegative),
                     abstractValue));

      Node bl = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(
                  kind::FLOATINGPOINT_LEQ, concrete[0], floatBelowAbstract),
              nm->mkNode(kind::LEQ, abstract, abstractValue)));
      handleLemma(bl);
      // TODO : see if the overflow conditions could be improved #1914

      return true;
    }
    else
    {
      // No refinement needed
      return false;
    }
  }
  else if (k == kind::FLOATINGPOINT_TO_FP_REAL)
  {
    // Get the values
    Assert(m->hasTerm(abstract));
    Assert(m->hasTerm(concrete[0]));
    Assert(m->hasTerm(concrete[1]));

    Node abstractValue = m->getValue(abstract);
    Node rmValue = m->getValue(concrete[0]);
    Node realValue = m->getValue(concrete[1]);

    Assert(abstractValue.isConst());
    Assert(rmValue.isConst());
    Assert(realValue.isConst());

    // Work out the actual value for those args
    NodeManager *nm = NodeManager::currentNM();

    Node evaluate =
        nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
                   nm->mkConst(FloatingPointToFPReal(
                       concrete.getType().getConst<FloatingPointSize>())),
                   rmValue,
                   realValue);
    Node concreteValue = Rewriter::rewrite(evaluate);
    Assert(concreteValue.isConst());

    Trace("fp-refineAbstraction")
        << "TheoryFp::refineAbstraction(): " << concrete[0] << " = " << rmValue
        << std::endl
        << "TheoryFp::refineAbstraction(): " << concrete[1] << " = "
        << realValue << std::endl
        << "TheoryFp::refineAbstraction(): " << abstract << " = "
        << abstractValue << std::endl
        << "TheoryFp::refineAbstraction(): " << concrete << " = "
        << concreteValue << std::endl;

    if (abstractValue != concreteValue)
    {
      Assert(!abstractValue.getConst<FloatingPoint>().isNaN());
      Assert(!concreteValue.getConst<FloatingPoint>().isNaN());

      Node correctRoundingMode = nm->mkNode(kind::EQUAL, concrete[0], rmValue);
      // TODO : Generalise to all rounding modes  #1914

      // First the "forward" constraints
      Node fg = nm->mkNode(
          kind::IMPLIES,
          correctRoundingMode,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(kind::GEQ, concrete[1], realValue),
              nm->mkNode(kind::FLOATINGPOINT_GEQ, abstract, concreteValue)));
      handleLemma(fg);

      Node fl = nm->mkNode(
          kind::IMPLIES,
          correctRoundingMode,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(kind::LEQ, concrete[1], realValue),
              nm->mkNode(kind::FLOATINGPOINT_LEQ, abstract, concreteValue)));
      handleLemma(fl);

      // Then the backwards constraints
      if (!abstractValue.getConst<FloatingPoint>().isInfinite())
      {
        Node realValueOfAbstract =
            Rewriter::rewrite(nm->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
                                         abstractValue,
                                         nm->mkConst(Rational(0U))));

        Node bg = nm->mkNode(
            kind::IMPLIES,
            correctRoundingMode,
            nm->mkNode(
                kind::EQUAL,
                nm->mkNode(kind::GEQ, concrete[1], realValueOfAbstract),
                nm->mkNode(kind::FLOATINGPOINT_GEQ, abstract, abstractValue)));
        handleLemma(bg);

        Node bl = nm->mkNode(
            kind::IMPLIES,
            correctRoundingMode,
            nm->mkNode(
                kind::EQUAL,
                nm->mkNode(kind::LEQ, concrete[1], realValueOfAbstract),
                nm->mkNode(kind::FLOATINGPOINT_LEQ, abstract, abstractValue)));
        handleLemma(bl);
      }

      return true;
    }
    else
    {
      // No refinement needed
      return false;
    }
  }
  else
  {
    Unreachable() << "Unknown abstraction";
  }

  return false;
}

void TheoryFp::convertAndEquateTerm(TNode node) {
  Trace("fp-convertTerm") << "TheoryFp::convertTerm(): " << node << std::endl;
  size_t oldAdditionalAssertions = d_conv.d_additionalAssertions.size();

  Node converted(d_conv.convert(node));

  if (converted != node) {
    Debug("fp-convertTerm")
        << "TheoryFp::convertTerm(): before " << node << std::endl;
    Debug("fp-convertTerm")
        << "TheoryFp::convertTerm(): after  " << converted << std::endl;
  }

  size_t newAdditionalAssertions = d_conv.d_additionalAssertions.size();
  Assert(oldAdditionalAssertions <= newAdditionalAssertions);

  while (oldAdditionalAssertions < newAdditionalAssertions) {
    Node addA = d_conv.d_additionalAssertions[oldAdditionalAssertions];

    Debug("fp-convertTerm") << "TheoryFp::convertTerm(): additional assertion  "
                            << addA << std::endl;

#ifdef SYMFPUPROPISBOOL
    handleLemma(addA, false, true);
#else
    NodeManager *nm = NodeManager::currentNM();

    handleLemma(
        nm->mkNode(kind::EQUAL, addA, nm->mkConst(::CVC4::BitVector(1U, 1U))));
#endif

    ++oldAdditionalAssertions;
  }

  // Equate the floating-point atom and the converted one.
  // Also adds the bit-vectors to the bit-vector solver.
  if (node.getType().isBoolean()) {
    if (converted != node) {
      Assert(converted.getType().isBitVector());

      NodeManager *nm = NodeManager::currentNM();

#ifdef SYMFPUPROPISBOOL
      handleLemma(nm->mkNode(kind::EQUAL, node, converted));
#else
      handleLemma(
          nm->mkNode(kind::EQUAL, node,
                     nm->mkNode(kind::EQUAL, converted,
                                nm->mkConst(::CVC4::BitVector(1U, 1U)))));
#endif

    } else {
      Assert((node.getKind() == kind::EQUAL));
    }

  } else if (node.getType().isBitVector()) {
    if (converted != node) {
      Assert(converted.getType().isBitVector());

      handleLemma(
          NodeManager::currentNM()->mkNode(kind::EQUAL, node, converted));
    }
  }

  return;
}

void TheoryFp::registerTerm(TNode node) {
  Trace("fp-registerTerm") << "TheoryFp::registerTerm(): " << node << std::endl;

  if (!isRegistered(node)) {
    Kind k = node.getKind();
    Assert(k != kind::FLOATINGPOINT_TO_FP_GENERIC
           && k != kind::FLOATINGPOINT_SUB && k != kind::FLOATINGPOINT_EQ
           && k != kind::FLOATINGPOINT_GEQ && k != kind::FLOATINGPOINT_GT);

    bool success = d_registeredTerms.insert(node);
    (void)success;  // Only used for assertion
    Assert(success);

    // Add to the equality engine
    if (k == kind::EQUAL)
    {
      d_equalityEngine.addTriggerEquality(node);
    }
    else
    {
      d_equalityEngine.addTerm(node);
    }

    // Give the expansion of classifications in terms of equalities
    // This should make equality reasoning slightly more powerful.
    if ((k == kind::FLOATINGPOINT_ISNAN) || (k == kind::FLOATINGPOINT_ISZ)
        || (k == kind::FLOATINGPOINT_ISINF))
    {
      NodeManager *nm = NodeManager::currentNM();
      FloatingPointSize s = node[0].getType().getConst<FloatingPointSize>();
      Node equalityAlias = Node::null();

      if (k == kind::FLOATINGPOINT_ISNAN)
      {
        equalityAlias = nm->mkNode(
            kind::EQUAL, node[0], nm->mkConst(FloatingPoint::makeNaN(s)));
      }
      else if (k == kind::FLOATINGPOINT_ISZ)
      {
        equalityAlias = nm->mkNode(
            kind::OR,
            nm->mkNode(kind::EQUAL,
                       node[0],
                       nm->mkConst(FloatingPoint::makeZero(s, true))),
            nm->mkNode(kind::EQUAL,
                       node[0],
                       nm->mkConst(FloatingPoint::makeZero(s, false))));
      }
      else if (k == kind::FLOATINGPOINT_ISINF)
      {
        equalityAlias = nm->mkNode(
            kind::OR,
            nm->mkNode(kind::EQUAL,
                       node[0],
                       nm->mkConst(FloatingPoint::makeInf(s, true))),
            nm->mkNode(kind::EQUAL,
                       node[0],
                       nm->mkConst(FloatingPoint::makeInf(s, false))));
      }
      else
      {
        Unreachable() << "Only isNaN, isInf and isZero have aliases";
      }

      handleLemma(nm->mkNode(kind::EQUAL, node, equalityAlias));
    }

    // Use symfpu to produce an equivalent bit-vector statement
    convertAndEquateTerm(node);
  }
  return;
}

bool TheoryFp::isRegistered(TNode node) {
  return !(d_registeredTerms.find(node) == d_registeredTerms.end());
}

void TheoryFp::preRegisterTerm(TNode node)
{
  if (Configuration::isBuiltWithSymFPU() && !options::fpExp())
  {
    TypeNode tn = node.getType();
    if (tn.isFloatingPoint())
    {
      unsigned exp_sz = tn.getFloatingPointExponentSize();
      unsigned sig_sz = tn.getFloatingPointSignificandSize();
      if (!((exp_sz == 8 && sig_sz == 24) || (exp_sz == 11 && sig_sz == 53)))
      {
        std::stringstream ss;
        ss << "FP term " << node << " with type whose size is " << exp_sz << "/"
           << sig_sz
           << " is not supported, only Float32 (8/24) or Float64 (11/53) types "
              "are supported in default mode. Try the experimental solver via "
              "--fp-exp. Note: There are known issues with the experimental "
              "solver, use at your own risk.";
        throw LogicException(ss.str());
      }
    }
  }
  Trace("fp-preRegisterTerm")
      << "TheoryFp::preRegisterTerm(): " << node << std::endl;
  registerTerm(node);
  return;
}

void TheoryFp::addSharedTerm(TNode node) {
  Trace("fp-addSharedTerm")
      << "TheoryFp::addSharedTerm(): " << node << std::endl;
  // A system-wide invariant; terms must be registered before they are shared
  Assert(isRegistered(node));
  return;
}

void TheoryFp::handleLemma(Node node) {
  Trace("fp") << "TheoryFp::handleLemma(): asserting " << node << std::endl;

  d_out->lemma(node, false,
               true);  // Has to be true because it contains embedded ITEs
  // Ignore the LemmaStatus structure for now...

  return;
}

bool TheoryFp::handlePropagation(TNode node) {
  Trace("fp") << "TheoryFp::handlePropagation(): propagate " << node
              << std::endl;

  bool stat = d_out->propagate(node);

  if (!stat)
  {
    d_conflict = true;
  }
  return stat;
}

void TheoryFp::handleConflict(TNode node) {
  Trace("fp") << "TheoryFp::handleConflict(): conflict detected " << node
              << std::endl;

  d_conflictNode = node;
  d_conflict = true;
  d_out->conflict(node);
  return;
}

void TheoryFp::check(Effort level) {
  Trace("fp") << "TheoryFp::check(): started at effort level " << level
              << std::endl;

  while (!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.d_assertion;

    Debug("fp") << "TheoryFp::check(): processing " << fact << std::endl;

    // Only handle equalities; the rest should be handled by
    // the bit-vector theory

    bool negated = fact.getKind() == kind::NOT;
    TNode predicate = negated ? fact[0] : fact;

    if (predicate.getKind() == kind::EQUAL) {
      Assert(!(predicate[0].getType().isFloatingPoint()
               || predicate[0].getType().isRoundingMode())
             || isRegistered(predicate[0]));
      Assert(!(predicate[1].getType().isFloatingPoint()
               || predicate[1].getType().isRoundingMode())
             || isRegistered(predicate[1]));
      registerTerm(predicate);  // Needed for float equalities

      if (negated) {
        Debug("fp-eq") << "TheoryFp::check(): adding dis-equality " << fact[0]
                       << std::endl;
        d_equalityEngine.assertEquality(predicate, false, fact);

      } else {
        Debug("fp-eq") << "TheoryFp::check(): adding equality " << fact
                       << std::endl;
        d_equalityEngine.assertEquality(predicate, true, fact);
      }
    } else {
      // A system-wide invariant; predicates are registered before they are
      // asserted
      Assert(isRegistered(predicate));

      if (d_equalityEngine.isFunctionKind(predicate.getKind())) {
        Debug("fp-eq") << "TheoryFp::check(): adding predicate " << predicate
                       << " is " << !negated << std::endl;
        d_equalityEngine.assertPredicate(predicate, !negated, fact);
      }
    }
  }

  // Resolve the abstractions for the conversion lemmas
  //  if (level == EFFORT_COMBINATION) {
  if (level == EFFORT_LAST_CALL)
  {
    Trace("fp") << "TheoryFp::check(): checking abstractions" << std::endl;
    TheoryModel *m = getValuation().getModel();
    bool lemmaAdded = false;

    for (abstractionMapType::const_iterator i = abstractionMap.begin();
         i != abstractionMap.end();
         ++i)
    {
      if (m->hasTerm((*i).first))
      {  // Is actually used in the model
        lemmaAdded |= refineAbstraction(m, (*i).first, (*i).second);
      }
    }
  }

  Trace("fp") << "TheoryFp::check(): completed" << std::endl;

  /* Checking should be handled by the bit-vector engine */
  return;

} /* TheoryFp::check() */

void TheoryFp::setMasterEqualityEngine(eq::EqualityEngine *eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

Node TheoryFp::explain(TNode n) {
  Trace("fp") << "TheoryFp::explain(): explain " << n << std::endl;

  // All things we assert directly (and not via bit-vector) should
  // come from the equality engine so this should be sufficient...
  std::vector<TNode> assumptions;

  bool polarity = n.getKind() != kind::NOT;
  TNode atom = polarity ? n : n[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }

  return helper::buildConjunct(assumptions);
}

Node TheoryFp::getModelValue(TNode var) {
  return d_conv.getValue(d_valuation, var);
}

bool TheoryFp::collectModelInfo(TheoryModel *m)
{
  std::set<Node> relevantTerms;

  Trace("fp-collectModelInfo")
      << "TheoryFp::collectModelInfo(): begin" << std::endl;

  // Work out which variables are needed
  computeRelevantTerms(relevantTerms);

  if (Trace.isOn("fp-collectModelInfo")) {
    for (std::set<Node>::const_iterator i(relevantTerms.begin());
         i != relevantTerms.end(); ++i) {
      Trace("fp-collectModelInfo")
          << "TheoryFp::collectModelInfo(): relevantTerms " << *i << std::endl;
    }
  }

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::stack<TNode> working;
  std::set<TNode> relevantVariables;
  for (std::set<Node>::const_iterator i(relevantTerms.begin());
       i != relevantTerms.end(); ++i) {
    working.push(*i);
  }

  while (!working.empty()) {
    TNode current = working.top();
    working.pop();

    // Ignore things that have already been explored
    if (visited.find(current) == visited.end()) {
      visited.insert(current);

      TypeNode t(current.getType());

      if ((t.isRoundingMode() || t.isFloatingPoint()) &&
          this->isLeaf(current)) {
        relevantVariables.insert(current);
      }

      for (size_t i = 0; i < current.getNumChildren(); ++i) {
        working.push(current[i]);
      }
    }
  }

  for (std::set<TNode>::const_iterator i(relevantVariables.begin());
       i != relevantVariables.end(); ++i) {
    TNode node = *i;

    Trace("fp-collectModelInfo")
        << "TheoryFp::collectModelInfo(): relevantVariable " << node
        << std::endl;

    if (!m->assertEquality(node, d_conv.getValue(d_valuation, node), true))
    {
      return false;
    }

    if (Configuration::isAssertionBuild() && isLeaf(node) && !node.isConst()
        && node.getType().isFloatingPoint())
    {
      // Check that the equality engine has asssigned values to all the
      // components of `node` except `(sign node)` (the sign component is
      // assignable, meaning that the model builder can pick an arbitrary value
      // for it if it hasn't been assigned in the equality engine).
      NodeManager* nm = NodeManager::currentNM();
      Node compNaN = nm->mkNode(kind::FLOATINGPOINT_COMPONENT_NAN, node);
      Node compInf = nm->mkNode(kind::FLOATINGPOINT_COMPONENT_INF, node);
      Node compZero = nm->mkNode(kind::FLOATINGPOINT_COMPONENT_ZERO, node);
      Node compExponent =
          nm->mkNode(kind::FLOATINGPOINT_COMPONENT_EXPONENT, node);
      Node compSignificand =
          nm->mkNode(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, node);

      eq::EqualityEngine* ee = m->getEqualityEngine();
      Assert(ee->hasTerm(compNaN) && ee->getRepresentative(compNaN).isConst());
      Assert(ee->hasTerm(compInf) && ee->getRepresentative(compInf).isConst());
      Assert(ee->hasTerm(compZero)
             && ee->getRepresentative(compZero).isConst());
      Assert(ee->hasTerm(compExponent)
             && ee->getRepresentative(compExponent).isConst());
      Assert(ee->hasTerm(compSignificand));
      Assert(ee->getRepresentative(compSignificand).isConst());

      // At most one of the flags (NaN, inf, zero) can be set
      Node one = nm->mkConst(BitVector(1U, 1U));
      size_t numFlags = 0;
      numFlags += ee->getRepresentative(compNaN) == one ? 1 : 0;
      numFlags += ee->getRepresentative(compInf) == one ? 1 : 0;
      numFlags += ee->getRepresentative(compZero) == one ? 1 : 0;
      Assert(numFlags <= 1);
    }
  }

  return true;
}

bool TheoryFp::NotifyClass::eqNotifyTriggerEquality(TNode equality,
                                                    bool value) {
  Debug("fp-eq")
      << "TheoryFp::eqNotifyTriggerEquality(): call back as equality "
      << equality << " is " << value << std::endl;

  if (value) {
    return d_theorySolver.handlePropagation(equality);
  } else {
    return d_theorySolver.handlePropagation(equality.notNode());
  }
}

bool TheoryFp::NotifyClass::eqNotifyTriggerPredicate(TNode predicate,
                                                     bool value) {
  Debug("fp-eq")
      << "TheoryFp::eqNotifyTriggerPredicate(): call back as predicate "
      << predicate << " is " << value << std::endl;

  if (value) {
    return d_theorySolver.handlePropagation(predicate);
  } else {
    return d_theorySolver.handlePropagation(predicate.notNode());
  }
}

bool TheoryFp::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1,
                                                        TNode t2, bool value) {
  Debug("fp-eq") << "TheoryFp::eqNotifyTriggerTermEquality(): call back as "
                 << t1 << (value ? " = " : " != ") << t2 << std::endl;

  if (value) {
    return d_theorySolver.handlePropagation(t1.eqNode(t2));
  } else {
    return d_theorySolver.handlePropagation(t1.eqNode(t2).notNode());
  }
}

void TheoryFp::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  Debug("fp-eq") << "TheoryFp::eqNotifyConstantTermMerge(): call back as " << t1
                 << " = " << t2 << std::endl;

  std::vector<TNode> assumptions;
  d_theorySolver.d_equalityEngine.explainEquality(t1, t2, true, assumptions);

  Node conflict = helper::buildConjunct(assumptions);

  d_theorySolver.handleConflict(conflict);
}

}  // namespace fp
}  // namespace theory
}  // namespace CVC4
