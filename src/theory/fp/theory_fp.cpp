/*********************                                                        */
/*! \file theory_fp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/fp/theory_fp.h"
#include "theory/theory_model.h"

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

  Unreachable("to_fp generic not rewritten");
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
TheoryFp::TheoryFp(context::Context *c, context::UserContext *u,
                   OutputChannel &out, Valuation valuation,
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
      d_toRealMap(u) {
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
                       nm->mkFunctionType(t, nm->realType()),
                       "floatingpoint_to_real_infinity_and_NaN_case",
                       NodeManager::SKOLEM_EXACT_NAME);
    d_toRealMap.insert(t, fun);
  } else {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0]);
}

Node TheoryFp::expandDefinition(LogicRequest &lr, Node node) {
  Trace("fp-expandDefinition")
      << "TheoryFp::expandDefinition(): " << node << std::endl;

  if (!this->d_expansionRequested) {
    lr.widenLogic(
        THEORY_UF);  // Needed for conversions to/from real and min/max
    lr.widenLogic(THEORY_BV);
    this->d_expansionRequested = true;
  }

  Node res = node;

  if (node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC) {
    res = removeToFPGeneric::removeToFPGeneric(node);

  } else if (node.getKind() == kind::FLOATINGPOINT_MIN) {
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_MIN_TOTAL,
                                           node[0], node[1], minUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_MAX) {
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_MAX_TOTAL,
                                           node[0], node[1], maxUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_UBV) {
    FloatingPointToUBV info = node.getOperator().getConst<FloatingPointToUBV>();
    FloatingPointToUBVTotal newInfo(info);

    res =
        NodeManager::currentNM()->mkNode(  // kind::FLOATINGPOINT_TO_UBV_TOTAL,
            NodeManager::currentNM()->mkConst(newInfo), node[0], node[1],
            toUBVUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_SBV) {
    FloatingPointToSBV info = node.getOperator().getConst<FloatingPointToSBV>();
    FloatingPointToSBVTotal newInfo(info);

    res =
        NodeManager::currentNM()->mkNode(  // kind::FLOATINGPOINT_TO_SBV_TOTAL,
            NodeManager::currentNM()->mkConst(newInfo), node[0], node[1],
            toSBVUF(node));

  } else if (node.getKind() == kind::FLOATINGPOINT_TO_REAL) {
    res = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
                                           node[0], toRealUF(node));

  } else {
    // Do nothing
  }

  if (res != node) {
    Trace("fp-expandDefinition") << "TheoryFp::expandDefinition(): " << node
                                 << " rewritten to " << res << std::endl;
  }

  return res;
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
    bool success = d_registeredTerms.insert(node);
    (void)success;  // Only used for assertion
    Assert(success);

    // Add to the equality engine
    if (node.getKind() == kind::EQUAL) {
      d_equalityEngine.addTriggerEquality(node);
    } else {
      d_equalityEngine.addTerm(node);
    }

    convertAndEquateTerm(node);
  }
  return;
}

bool TheoryFp::isRegistered(TNode node) {
  return !(d_registeredTerms.find(node) == d_registeredTerms.end());
}

void TheoryFp::preRegisterTerm(TNode node) {
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

  if (!stat) handleConflict(node);

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
    TNode fact = assertion.assertion;

    Debug("fp") << "TheoryFp::check(): processing " << fact << std::endl;

    // Only handle equalities; the rest should be handled by
    // the bit-vector theory

    bool negated = fact.getKind() == kind::NOT;
    TNode predicate = negated ? fact[0] : fact;

    if (predicate.getKind() == kind::EQUAL) {
      Assert(!(predicate[0].getType().isFloatingPoint() ||
               predicate[0].getType().isRoundingMode()) ||
             isRegistered(predicate[0]));
      Assert(!(predicate[1].getType().isFloatingPoint() ||
               predicate[1].getType().isRoundingMode()) ||
             isRegistered(predicate[1]));
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
