/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of floating-point arithmetic.
 */

#include "theory/fp/theory_fp.h"

#include <set>
#include <stack>
#include <unordered_set>
#include <vector>

#include "base/configuration.h"
#include "expr/skolem_manager.h"
#include "options/fp_options.h"
#include "smt/logic_exception.h"
#include "theory/fp/fp_word_blaster.h"
#include "theory/fp/theory_fp_rewriter.h"
#include "theory/output_channel.h"
#include "theory/theory_model.h"
#include "util/floatingpoint.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace fp {

namespace helper {
Node buildConjunct(const std::vector<TNode> &assumptions) {
  if (assumptions.size() == 0) {
    return NodeManager::currentNM()->mkConst<bool>(true);

  } else if (assumptions.size() == 1) {
    return assumptions[0];

  } else {
    // \todo see bv::utils::flattenAnd

    NodeBuilder conjunction(kind::AND);
    for (std::vector<TNode>::const_iterator it = assumptions.begin();
         it != assumptions.end(); ++it) {
      conjunction << *it;
    }

    return conjunction;
  }
}
}  // namespace helper

/** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
TheoryFp::TheoryFp(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_FP, env, out, valuation),
      d_notification(*this),
      d_registeredTerms(userContext()),
      d_wordBlaster(new FpWordBlaster(userContext())),
      d_expansionRequested(false),
      d_abstractionMap(userContext()),
      d_rewriter(userContext()),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::fp::", true),
      d_wbFactsCache(userContext()),
      d_true(d_env.getNodeManager()->mkConst(true))
{
  // indicate we are using the default theory state and inference manager
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryRewriter* TheoryFp::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryFp::getProofChecker() { return nullptr; }

bool TheoryFp::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notification;
  esi.d_name = "theory::fp::ee";
  return true;
}

void TheoryFp::finishInit()
{
  Assert(d_equalityEngine != nullptr);
  // Kinds that are to be handled in the congruence closure

  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ABS);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_NEG);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ADD);
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_SUB); // Removed
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_MULT);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_DIV);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_FMA);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_SQRT);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_REM);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_RTI);
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_MIN); // Removed
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_MAX); // Removed
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_MIN_TOTAL);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_MAX_TOTAL);

  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_EQ); // Removed
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_LEQ);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_LT);
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_GEQ); // Removed
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_GT); // Removed
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISN);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISSN);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISZ);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISINF);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISNAN);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISNEG);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_ISPOS);

  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_FP_REAL);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR);
  d_equalityEngine->addFunctionKind(
      kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR);
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_FP_GENERIC); //
  // Needed in parsing, should be rewritten away

  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_UBV); // Removed
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_SBV); // Removed
  // d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_REAL); // Removed
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_UBV_TOTAL);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_SBV_TOTAL);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_TO_REAL_TOTAL);

  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_COMPONENT_NAN);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_COMPONENT_INF);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_COMPONENT_ZERO);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGN);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_COMPONENT_EXPONENT);
  d_equalityEngine->addFunctionKind(kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);
  d_equalityEngine->addFunctionKind(kind::ROUNDINGMODE_BITBLAST);
}

TrustNode TheoryFp::ppRewrite(TNode node, std::vector<SkolemLemma>& lems)
{
  Trace("fp-ppRewrite") << "TheoryFp::ppRewrite(): " << node << std::endl;
  // first, see if we need to expand definitions
  TrustNode texp = d_rewriter.expandDefinition(node);
  if (!texp.isNull())
  {
    return texp;
  }

  Node res = node;


  if (res != node)
  {
    Trace("fp-ppRewrite") << "TheoryFp::ppRewrite(): node " << node
                          << " rewritten to " << res << std::endl;
    return TrustNode::mkTrustRewrite(node, res, nullptr);
  }

  return TrustNode::null();
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

    Assert(!abstractValue.isNull());
    Assert(!floatValue.isNull());
    Assert(!undefValue.isNull());
    Assert(abstractValue.isConst());
    Assert(floatValue.isConst());
    Assert(undefValue.isConst());

    // Work out the actual value for those args
    NodeManager *nm = NodeManager::currentNM();

    Node evaluate =
        nm->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL, floatValue, undefValue);
    Node concreteValue = rewrite(evaluate);
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
      handleLemma(fg, InferenceId::FP_PREPROCESS);

      Node fl = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(kind::FLOATINGPOINT_LEQ, concrete[0], floatValue),
              nm->mkNode(kind::LEQ, abstract, concreteValue)));
      handleLemma(fl, InferenceId::FP_PREPROCESS);

      // Then the backwards constraints
      Node floatAboveAbstract = rewrite(
          nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
                     nm->mkConst(FloatingPointToFPReal(
                         concrete[0].getType().getConst<FloatingPointSize>())),
                     nm->mkConst(RoundingMode::ROUND_TOWARD_POSITIVE),
                     abstractValue));

      Node bg = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(
                  kind::FLOATINGPOINT_GEQ, concrete[0], floatAboveAbstract),
              nm->mkNode(kind::GEQ, abstract, abstractValue)));
      handleLemma(bg, InferenceId::FP_PREPROCESS);

      Node floatBelowAbstract = rewrite(
          nm->mkNode(kind::FLOATINGPOINT_TO_FP_REAL,
                     nm->mkConst(FloatingPointToFPReal(
                         concrete[0].getType().getConst<FloatingPointSize>())),
                     nm->mkConst(RoundingMode::ROUND_TOWARD_NEGATIVE),
                     abstractValue));

      Node bl = nm->mkNode(
          kind::IMPLIES,
          defined,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(
                  kind::FLOATINGPOINT_LEQ, concrete[0], floatBelowAbstract),
              nm->mkNode(kind::LEQ, abstract, abstractValue)));
      handleLemma(bl, InferenceId::FP_PREPROCESS);
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
    Assert(m->hasTerm(abstract)) << "Term " << abstract << " not in model";
    Assert(m->hasTerm(concrete[0]))
        << "Term " << concrete[0] << " not in model";
    // Note: while the value for concrete[1] that we get from the model has to
    // be const, it is not necessarily the case that `m->hasTerm(concrete[1])`.
    // The arithmetic solver computes values for the variables in shared terms
    // but does not necessarily add the shared terms themselves.

    Node abstractValue = m->getValue(abstract);
    Node rmValue = m->getValue(concrete[0]);
    Node realValue = m->getValue(concrete[1]);

    Assert(!abstractValue.isNull());
    Assert(!rmValue.isNull());
    Assert(!realValue.isNull());
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
    Node concreteValue = rewrite(evaluate);
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
      handleLemma(fg, InferenceId::FP_PREPROCESS);

      Node fl = nm->mkNode(
          kind::IMPLIES,
          correctRoundingMode,
          nm->mkNode(
              kind::EQUAL,
              nm->mkNode(kind::LEQ, concrete[1], realValue),
              nm->mkNode(kind::FLOATINGPOINT_LEQ, abstract, concreteValue)));
      handleLemma(fl, InferenceId::FP_PREPROCESS);

      // Then the backwards constraints
      if (!abstractValue.getConst<FloatingPoint>().isInfinite())
      {
        Node realValueOfAbstract =
            rewrite(nm->mkNode(kind::FLOATINGPOINT_TO_REAL_TOTAL,
                               abstractValue,
                               nm->mkConst(CONST_RATIONAL, Rational(0U))));

        Node bg = nm->mkNode(
            kind::IMPLIES,
            correctRoundingMode,
            nm->mkNode(
                kind::EQUAL,
                nm->mkNode(kind::GEQ, concrete[1], realValueOfAbstract),
                nm->mkNode(kind::FLOATINGPOINT_GEQ, abstract, abstractValue)));
        handleLemma(bg, InferenceId::FP_PREPROCESS);

        Node bl = nm->mkNode(
            kind::IMPLIES,
            correctRoundingMode,
            nm->mkNode(
                kind::EQUAL,
                nm->mkNode(kind::LEQ, concrete[1], realValueOfAbstract),
                nm->mkNode(kind::FLOATINGPOINT_LEQ, abstract, abstractValue)));
        handleLemma(bl, InferenceId::FP_PREPROCESS);
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

void TheoryFp::wordBlastAndEquateTerm(TNode node)
{
  Trace("fp-wordBlastTerm")
      << "TheoryFp::wordBlastTerm(): " << node << std::endl;

  size_t oldSize = d_wordBlaster->d_additionalAssertions.size();

  Node wordBlasted(d_wordBlaster->wordBlast(node));

  size_t newSize = d_wordBlaster->d_additionalAssertions.size();

  if (wordBlasted != node)
  {
    Debug("fp-wordBlastTerm")
        << "TheoryFp::wordBlastTerm(): before " << node << std::endl;
    Debug("fp-wordBlastTerm")
        << "TheoryFp::wordBlastTerm(): after  " << wordBlasted << std::endl;
  }

  Assert(oldSize <= newSize);

  while (oldSize < newSize)
  {
    Node addA = d_wordBlaster->d_additionalAssertions[oldSize];

    Debug("fp-wordBlastTerm")
        << "TheoryFp::wordBlastTerm(): additional assertion  " << addA
        << std::endl;

    NodeManager* nm = NodeManager::currentNM();

    handleLemma(
        nm->mkNode(kind::EQUAL, addA, nm->mkConst(::cvc5::BitVector(1U, 1U))),
        InferenceId::FP_EQUATE_TERM);

    ++oldSize;
  }

  // Equate the floating-point atom and the wordBlasted one.
  // Also adds the bit-vectors to the bit-vector solver.
  if (node.getType().isBoolean())
  {
    if (wordBlasted != node)
    {
      Assert(wordBlasted.getType().isBitVector());

      NodeManager* nm = NodeManager::currentNM();

      handleLemma(
          nm->mkNode(kind::EQUAL,
                     node,
                     nm->mkNode(kind::EQUAL,
                                wordBlasted,
                                nm->mkConst(::cvc5::BitVector(1U, 1U)))),
          InferenceId::FP_EQUATE_TERM);
    }
    else
    {
      Assert((node.getKind() == kind::EQUAL));
    }
  }
  else if (node.getType().isBitVector())
  {
    if (wordBlasted != node)
    {
      Assert(wordBlasted.getType().isBitVector());

      handleLemma(
          NodeManager::currentNM()->mkNode(kind::EQUAL, node, wordBlasted),
          InferenceId::FP_EQUATE_TERM);
    }
  }

  return;
}

void TheoryFp::registerTerm(TNode node)
{
  Trace("fp-registerTerm") << "TheoryFp::registerTerm(): " << node << std::endl;

  Kind k = node.getKind();
  Assert(k != kind::FLOATINGPOINT_TO_FP_GENERIC && k != kind::FLOATINGPOINT_SUB
         && k != kind::FLOATINGPOINT_EQ && k != kind::FLOATINGPOINT_GEQ
         && k != kind::FLOATINGPOINT_GT);

  // Add to the equality engine, always. This is required to ensure
  // getEqualityStatus works as expected when theory combination is enabled.
  if (k == kind::EQUAL)
  {
    d_equalityEngine->addTriggerPredicate(node);
  }
  else
  {
    d_equalityEngine->addTerm(node);
  }

  // if not registered in this user context
  if (isRegistered(node))
  {
    return;
  }

  CVC5_UNUSED bool success = d_registeredTerms.insert(node);
  Assert(success);

  // Give the expansion of classifications in terms of equalities
  // This should make equality reasoning slightly more powerful.
  if ((k == kind::FLOATINGPOINT_ISNAN) || (k == kind::FLOATINGPOINT_ISZ)
      || (k == kind::FLOATINGPOINT_ISINF))
  {
    NodeManager* nm = NodeManager::currentNM();
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
      equalityAlias =
          nm->mkNode(kind::OR,
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

    handleLemma(nm->mkNode(kind::EQUAL, node, equalityAlias),
                InferenceId::FP_REGISTER_TERM);
  }
  else if (k == kind::FLOATINGPOINT_TO_REAL_TOTAL)
  {
    // Purify (fp.to_real x)
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node sk = sm->mkPurifySkolem(node, "to_real", "fp purify skolem");
    handleLemma(node.eqNode(sk), InferenceId::FP_REGISTER_TERM);
    d_abstractionMap.insert(sk, node);

    Node pd =
        nm->mkNode(kind::IMPLIES,
                   nm->mkNode(kind::OR,
                              nm->mkNode(kind::FLOATINGPOINT_ISNAN, node[0]),
                              nm->mkNode(kind::FLOATINGPOINT_ISINF, node[0])),
                   nm->mkNode(kind::EQUAL, node, node[1]));
    handleLemma(pd, InferenceId::FP_REGISTER_TERM);

    Node z = nm->mkNode(
        kind::IMPLIES,
        nm->mkNode(kind::FLOATINGPOINT_ISZ, node[0]),
        nm->mkNode(
            kind::EQUAL, node, nm->mkConst(CONST_RATIONAL, Rational(0U))));
    handleLemma(z, InferenceId::FP_REGISTER_TERM);
    return;

    // TODO : bounds on the output from largest floats, #1914
  }
  else if (k == kind::FLOATINGPOINT_TO_FP_REAL)
  {
    // Purify ((_ to_fp eb sb) rm x)
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node sk = sm->mkPurifySkolem(node, "to_real_fp", "fp purify skolem");
    handleLemma(node.eqNode(sk), InferenceId::FP_REGISTER_TERM);
    d_abstractionMap.insert(sk, node);

    Node nnan =
        nm->mkNode(kind::NOT, nm->mkNode(kind::FLOATINGPOINT_ISNAN, node));
    handleLemma(nnan, InferenceId::FP_REGISTER_TERM);

    Node z = nm->mkNode(
        kind::IMPLIES,
        nm->mkNode(
            kind::EQUAL, node[1], nm->mkConst(CONST_RATIONAL, Rational(0U))),
        nm->mkNode(kind::EQUAL,
                   node,
                   nm->mkConst(FloatingPoint::makeZero(
                       node.getType().getConst<FloatingPointSize>(), false))));
    handleLemma(z, InferenceId::FP_REGISTER_TERM);
    return;

    // TODO : rounding-mode specific bounds on floats that don't give infinity
    // BEWARE of directed rounding!   #1914
  }

  /* When not word-blasting lazier, we word-blast every term on
   * registration. */
  if (!options().fp.fpLazyWb)
  {
    wordBlastAndEquateTerm(node);
  }
}

bool TheoryFp::isRegistered(TNode node)
{
  return d_registeredTerms.find(node) != d_registeredTerms.end();
}

void TheoryFp::preRegisterTerm(TNode node)
{
  if (!options().fp.fpExp)
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

void TheoryFp::handleLemma(Node node, InferenceId id)
{
  Trace("fp") << "TheoryFp::handleLemma(): asserting " << node << std::endl;
  if (rewrite(node) != d_true)
  {
    /* We only send non-trivial lemmas. */
    d_im.lemma(node, id);
  }
}

bool TheoryFp::propagateLit(TNode node)
{
  Trace("fp") << "TheoryFp::propagateLit(): propagate " << node << std::endl;
  return d_im.propagateLit(node);
}

void TheoryFp::conflictEqConstantMerge(TNode t1, TNode t2)
{
  Trace("fp") << "TheoryFp::conflictEqConstantMerge(): conflict detected"
              << std::endl;
  d_im.conflictEqConstantMerge(t1, t2);
}

bool TheoryFp::needsCheckLastEffort()
{
  // only need to check if we have added to the abstraction map, otherwise
  // postCheck below is a no-op.
  return !d_abstractionMap.empty();
}

void TheoryFp::postCheck(Effort level)
{
  /* Resolve the abstractions for the conversion lemmas */
  if (level == EFFORT_LAST_CALL)
  {
    Trace("fp-abstraction")
        << "TheoryFp::check(): checking abstractions" << std::endl;
    TheoryModel* m = getValuation().getModel();
    bool lemmaAdded = false;

    for (const auto& [abstract, concrete] : d_abstractionMap)
    {
      Trace("fp-abstraction")
          << "TheoryFp::check(): Abstraction: " << abstract << std::endl;
      if (m->hasTerm(abstract))
      {  // Is actually used in the model
        Trace("fp-abstraction")
            << "TheoryFp::check(): ... relevant" << std::endl;
        lemmaAdded |= refineAbstraction(m, abstract, concrete);
      }
      else
      {
        Trace("fp-abstraction")
            << "TheoryFp::check(): ... not relevant" << std::endl;
      }
    }
  }

  Trace("fp") << "TheoryFp::check(): completed" << std::endl;
  /* Checking should be handled by the bit-vector engine */
}

bool TheoryFp::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  /* Word-blast lazier if configured. */
  if (options().fp.fpLazyWb
      && d_wbFactsCache.find(atom) == d_wbFactsCache.end())
  {
    d_wbFactsCache.insert(atom);
    wordBlastAndEquateTerm(atom);
  }

  if (atom.getKind() == kind::EQUAL)
  {
    Assert(!(atom[0].getType().isFloatingPoint()
             || atom[0].getType().isRoundingMode())
           || isRegistered(atom[0]));
    Assert(!(atom[1].getType().isFloatingPoint()
             || atom[1].getType().isRoundingMode())
           || isRegistered(atom[1]));
    registerTerm(atom);  // Needed for float equalities
  }
  else
  {
    // A system-wide invariant; predicates are registered before they are
    // asserted
    Assert(isRegistered(atom));

    if (!d_equalityEngine->isFunctionKind(atom.getKind()))
    {
      return true;
    }
  }
  return false;
}

void TheoryFp::notifySharedTerm(TNode n)
{
  /* Word-blast lazier if configured. */
  if (options().fp.fpLazyWb && d_wbFactsCache.find(n) == d_wbFactsCache.end())
  {
    d_wbFactsCache.insert(n);
    wordBlastAndEquateTerm(n);
  }
}

TrustNode TheoryFp::explain(TNode n)
{
  Trace("fp") << "TheoryFp::explain(): explain " << n << std::endl;

  // All things we assert directly (and not via bit-vector) should
  // come from the equality engine so this should be sufficient...
  std::vector<TNode> assumptions;

  bool polarity = n.getKind() != kind::NOT;
  TNode atom = polarity ? n : n[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions);
  }

  Node exp = helper::buildConjunct(assumptions);
  return TrustNode::mkTrustPropExp(n, exp, nullptr);
}

Node TheoryFp::getModelValue(TNode var) {
  return d_wordBlaster->getValue(d_valuation, var);
}

bool TheoryFp::collectModelInfo(TheoryModel* m,
                                const std::set<Node>& relevantTerms)
{
  // this override behavior to not assert equality engine
  return collectModelValues(m, relevantTerms);
}

bool TheoryFp::collectModelValues(TheoryModel* m,
                                  const std::set<Node>& relevantTerms)
{
  Trace("fp-collectModelInfo")
      << "TheoryFp::collectModelInfo(): begin" << std::endl;
  if (Trace.isOn("fp-collectModelInfo")) {
    for (std::set<Node>::const_iterator i(relevantTerms.begin());
         i != relevantTerms.end(); ++i) {
      Trace("fp-collectModelInfo")
          << "TheoryFp::collectModelInfo(): relevantTerms " << *i << std::endl;
    }
  }

  std::unordered_set<TNode> visited;
  std::vector<TNode> working;
  std::set<TNode> relevantVariables;
  for (const Node& n : relevantTerms)
  {
    working.emplace_back(n);
  }

  while (!working.empty()) {
    TNode current = working.back();
    working.pop_back();

    if (visited.find(current) != visited.end())
    {
      // Ignore things that have already been explored
      continue;
    }
    visited.insert(current);

    TypeNode t = current.getType();

    if ((t.isRoundingMode() || t.isFloatingPoint()) && this->isLeaf(current))
    {
      relevantVariables.insert(current);
    }

    working.insert(working.end(), current.begin(), current.end());
  }

  for (const TNode& node : relevantVariables)
  {
    Trace("fp-collectModelInfo")
        << "TheoryFp::collectModelInfo(): relevantVariable " << node
        << std::endl;

    Node wordBlasted = d_wordBlaster->getValue(d_valuation, node);
    // We only assign the value if the FpWordBlaster actually has one, that is,
    // if FpWordBlaster::getValue() does not return a null node.
    if (!wordBlasted.isNull() && !m->assertEquality(node, wordBlasted, true))
    {
      Trace("fp-collectModelInfo")
          << "TheoryFp::collectModelInfo(): ... not converted" << std::endl;
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

bool TheoryFp::NotifyClass::eqNotifyTriggerPredicate(TNode predicate,
                                                     bool value) {
  Debug("fp-eq")
      << "TheoryFp::eqNotifyTriggerPredicate(): call back as predicate "
      << predicate << " is " << value << std::endl;

  if (value) {
    return d_theorySolver.propagateLit(predicate);
  }
  return d_theorySolver.propagateLit(predicate.notNode());
}

bool TheoryFp::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1,
                                                        TNode t2, bool value) {
  Debug("fp-eq") << "TheoryFp::eqNotifyTriggerTermEquality(): call back as "
                 << t1 << (value ? " = " : " != ") << t2 << std::endl;

  if (value) {
    return d_theorySolver.propagateLit(t1.eqNode(t2));
  }
  return d_theorySolver.propagateLit(t1.eqNode(t2).notNode());
}

void TheoryFp::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  Debug("fp-eq") << "TheoryFp::eqNotifyConstantTermMerge(): call back as " << t1
                 << " = " << t2 << std::endl;
  d_theorySolver.conflictEqConstantMerge(t1, t2);
}

}  // namespace fp
}  // namespace theory
}  // namespace cvc5
