/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include <unordered_map>
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
using namespace cvc5::internal::kind;

namespace cvc5::internal {
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

    NodeBuilder conjunction(Kind::AND);
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
      d_wordBlaster(new FpWordBlaster(userContext())),
      d_registeredTerms(userContext()),
      d_abstractionMap(userContext()),
      d_rewriter(nodeManager(), userContext()),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::fp::", true),
      d_notify(d_im),
      d_wbFactsCache(userContext()),
      d_invalidateModelCache(context(), true),
      d_true(NodeManager::currentNM()->mkConst(true))
{
  // indicate we are using the default theory state and inference manager
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryRewriter* TheoryFp::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryFp::getProofChecker() { return nullptr; }

bool TheoryFp::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::fp::ee";
  return true;
}

void TheoryFp::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // Kinds that are to be handled in the congruence closure
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_ABS);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_NEG);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_ADD);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_MULT);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_DIV);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_FMA);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_SQRT);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_REM);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_RTI);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_MIN_TOTAL);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_MAX_TOTAL);

  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_LEQ);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_LT);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_NORMAL);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_SUBNORMAL);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_ZERO);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_INF);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_NAN);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_NEG);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_IS_POS);

  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_FP_FROM_FP);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_FP_FROM_REAL);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_FP_FROM_SBV);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_FP_FROM_UBV);

  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_UBV_TOTAL);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_SBV_TOTAL);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_TO_REAL_TOTAL);

  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_COMPONENT_NAN);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_COMPONENT_INF);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_COMPONENT_ZERO);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_COMPONENT_SIGN);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_COMPONENT_EXPONENT);
  d_equalityEngine->addFunctionKind(Kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);
  d_equalityEngine->addFunctionKind(Kind::ROUNDINGMODE_BITBLAST);
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

  // The following kinds should have been removed by the
  // rewriter/expandDefinition
  Assert(node.getKind() != Kind::FLOATINGPOINT_SUB
         && node.getKind() != Kind::FLOATINGPOINT_MIN
         && node.getKind() != Kind::FLOATINGPOINT_MAX
         && node.getKind() != Kind::FLOATINGPOINT_EQ
         && node.getKind() != Kind::FLOATINGPOINT_GEQ
         && node.getKind() != Kind::FLOATINGPOINT_GT
         && node.getKind() != Kind::FLOATINGPOINT_TO_UBV
         && node.getKind() != Kind::FLOATINGPOINT_TO_SBV
         && node.getKind() != Kind::FLOATINGPOINT_TO_REAL)
      << "Expected floating-point kind " << node.getKind() << " to be removed";

  return TrustNode::null();
}

bool TheoryFp::refineAbstraction(TheoryModel *m, TNode abstract, TNode concrete)
{
  Trace("fp-refineAbstraction") << "TheoryFp::refineAbstraction(): " << abstract
                                << " vs. " << concrete << std::endl;
  Kind k = concrete.getKind();
  if (k == Kind::FLOATINGPOINT_TO_REAL_TOTAL)
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
        nm->mkNode(Kind::FLOATINGPOINT_TO_REAL_TOTAL, floatValue, undefValue);
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
          Kind::AND,
          nm->mkNode(Kind::NOT,
                     nm->mkNode(Kind::FLOATINGPOINT_IS_NAN, concrete[0])),
          nm->mkNode(Kind::NOT,
                     nm->mkNode(Kind::FLOATINGPOINT_IS_INF, concrete[0])));
      // First the "forward" constraints
      Node fg = nm->mkNode(
          Kind::IMPLIES,
          defined,
          nm->mkNode(
              Kind::EQUAL,
              nm->mkNode(Kind::FLOATINGPOINT_GEQ, concrete[0], floatValue),
              nm->mkNode(Kind::GEQ, abstract, concreteValue)));
      handleLemma(fg, InferenceId::FP_PREPROCESS);

      Node fl = nm->mkNode(
          Kind::IMPLIES,
          defined,
          nm->mkNode(
              Kind::EQUAL,
              nm->mkNode(Kind::FLOATINGPOINT_LEQ, concrete[0], floatValue),
              nm->mkNode(Kind::LEQ, abstract, concreteValue)));
      handleLemma(fl, InferenceId::FP_PREPROCESS);

      // Then the backwards constraints
      Node floatAboveAbstract = rewrite(
          nm->mkNode(Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
                     nm->mkConst(FloatingPointToFPReal(
                         concrete[0].getType().getConst<FloatingPointSize>())),
                     nm->mkConst(RoundingMode::ROUND_TOWARD_POSITIVE),
                     abstractValue));

      Node bg = nm->mkNode(
          Kind::IMPLIES,
          defined,
          nm->mkNode(
              Kind::EQUAL,
              nm->mkNode(
                  Kind::FLOATINGPOINT_GEQ, concrete[0], floatAboveAbstract),
              nm->mkNode(Kind::GEQ, abstract, abstractValue)));
      handleLemma(bg, InferenceId::FP_PREPROCESS);

      Node floatBelowAbstract = rewrite(
          nm->mkNode(Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
                     nm->mkConst(FloatingPointToFPReal(
                         concrete[0].getType().getConst<FloatingPointSize>())),
                     nm->mkConst(RoundingMode::ROUND_TOWARD_NEGATIVE),
                     abstractValue));

      Node bl = nm->mkNode(
          Kind::IMPLIES,
          defined,
          nm->mkNode(
              Kind::EQUAL,
              nm->mkNode(
                  Kind::FLOATINGPOINT_LEQ, concrete[0], floatBelowAbstract),
              nm->mkNode(Kind::LEQ, abstract, abstractValue)));
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
  else if (k == Kind::FLOATINGPOINT_TO_FP_FROM_REAL)
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
        nm->mkNode(Kind::FLOATINGPOINT_TO_FP_FROM_REAL,
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

      Node correctRoundingMode = nm->mkNode(Kind::EQUAL, concrete[0], rmValue);
      // TODO : Generalise to all rounding modes  #1914

      // First the "forward" constraints
      Node fg = nm->mkNode(
          Kind::IMPLIES,
          correctRoundingMode,
          nm->mkNode(
              Kind::EQUAL,
              nm->mkNode(Kind::GEQ, concrete[1], realValue),
              nm->mkNode(Kind::FLOATINGPOINT_GEQ, abstract, concreteValue)));
      handleLemma(fg, InferenceId::FP_PREPROCESS);

      Node fl = nm->mkNode(
          Kind::IMPLIES,
          correctRoundingMode,
          nm->mkNode(
              Kind::EQUAL,
              nm->mkNode(Kind::LEQ, concrete[1], realValue),
              nm->mkNode(Kind::FLOATINGPOINT_LEQ, abstract, concreteValue)));
      handleLemma(fl, InferenceId::FP_PREPROCESS);

      // Then the backwards constraints
      if (!abstractValue.getConst<FloatingPoint>().isInfinite())
      {
        Node realValueOfAbstract =
            rewrite(nm->mkNode(Kind::FLOATINGPOINT_TO_REAL_TOTAL,
                               abstractValue,
                               nm->mkConstReal(Rational(0U))));

        Node bg = nm->mkNode(
            Kind::IMPLIES,
            correctRoundingMode,
            nm->mkNode(
                Kind::EQUAL,
                nm->mkNode(Kind::GEQ, concrete[1], realValueOfAbstract),
                nm->mkNode(Kind::FLOATINGPOINT_GEQ, abstract, abstractValue)));
        handleLemma(bg, InferenceId::FP_PREPROCESS);

        Node bl = nm->mkNode(
            Kind::IMPLIES,
            correctRoundingMode,
            nm->mkNode(
                Kind::EQUAL,
                nm->mkNode(Kind::LEQ, concrete[1], realValueOfAbstract),
                nm->mkNode(Kind::FLOATINGPOINT_LEQ, abstract, abstractValue)));
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

  if (TraceIsOn("fp-wordBlastTerm") && wordBlasted != node)
  {
    Trace("fp-wordBlastTerm")
        << "TheoryFp::wordBlastTerm(): before " << node << std::endl;
    Trace("fp-wordBlastTerm")
        << "TheoryFp::wordBlastTerm(): after  " << wordBlasted << std::endl;
  }

  Assert(oldSize <= newSize);

  while (oldSize < newSize)
  {
    Node addA = d_wordBlaster->d_additionalAssertions[oldSize];

    Trace("fp-wordBlastTerm")
        << "TheoryFp::wordBlastTerm(): additional assertion  " << addA
        << std::endl;

    NodeManager* nm = NodeManager::currentNM();

    handleLemma(
        nm->mkNode(
            Kind::EQUAL, addA, nm->mkConst(cvc5::internal::BitVector(1U, 1U))),
        InferenceId::FP_EQUATE_TERM);

    ++oldSize;
  }

  // Equate the floating-point atom and the wordBlasted one.
  // Adds the bit-vectors to the bit-vector solver via sending the equality
  // as lemma to the inference manager.
  if (node.getType().isBoolean())
  {
    if (wordBlasted != node)
    {
      Assert(wordBlasted.getType().isBitVector());

      NodeManager* nm = NodeManager::currentNM();

      handleLemma(
          nm->mkNode(
              Kind::EQUAL,
              node,
              nm->mkNode(Kind::EQUAL,
                         wordBlasted,
                         nm->mkConst(cvc5::internal::BitVector(1U, 1U)))),
          InferenceId::FP_EQUATE_TERM);
    }
    else
    {
      Assert((node.getKind() == Kind::EQUAL));
    }
  }
  else if (node.getType().isBitVector())
  {
    if (wordBlasted != node)
    {
      Assert(wordBlasted.getType().isBitVector());

      handleLemma(
          NodeManager::currentNM()->mkNode(Kind::EQUAL, node, wordBlasted),
          InferenceId::FP_EQUATE_TERM);
    }
  }

  return;
}

void TheoryFp::registerTerm(TNode node)
{
  Trace("fp-registerTerm") << "TheoryFp::registerTerm(): " << node << std::endl;

  Kind k = node.getKind();
  Assert(k != Kind::FLOATINGPOINT_SUB && k != Kind::FLOATINGPOINT_EQ
         && k != Kind::FLOATINGPOINT_GEQ && k != Kind::FLOATINGPOINT_GT);

  // Add to the equality engine, always. This is required to ensure
  // getEqualityStatus works as expected when theory combination is enabled.
  if (k == Kind::EQUAL)
  {
    d_state.addEqualityEngineTriggerPredicate(node);
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
  if ((k == Kind::FLOATINGPOINT_IS_NAN) || (k == Kind::FLOATINGPOINT_IS_ZERO)
      || (k == Kind::FLOATINGPOINT_IS_INF))
  {
    NodeManager* nm = NodeManager::currentNM();
    FloatingPointSize s = node[0].getType().getConst<FloatingPointSize>();
    Node equalityAlias = Node::null();

    if (k == Kind::FLOATINGPOINT_IS_NAN)
    {
      equalityAlias = nm->mkNode(
          Kind::EQUAL, node[0], nm->mkConst(FloatingPoint::makeNaN(s)));
    }
    else if (k == Kind::FLOATINGPOINT_IS_ZERO)
    {
      equalityAlias = nm->mkNode(
          Kind::OR,
          nm->mkNode(Kind::EQUAL,
                     node[0],
                     nm->mkConst(FloatingPoint::makeZero(s, true))),
          nm->mkNode(Kind::EQUAL,
                     node[0],
                     nm->mkConst(FloatingPoint::makeZero(s, false))));
    }
    else if (k == Kind::FLOATINGPOINT_IS_INF)
    {
      equalityAlias =
          nm->mkNode(Kind::OR,
                     nm->mkNode(Kind::EQUAL,
                                node[0],
                                nm->mkConst(FloatingPoint::makeInf(s, true))),
                     nm->mkNode(Kind::EQUAL,
                                node[0],
                                nm->mkConst(FloatingPoint::makeInf(s, false))));
    }
    else
    {
      Unreachable() << "Only isNaN, isInf and isZero have aliases";
    }

    handleLemma(nm->mkNode(Kind::EQUAL, node, equalityAlias),
                InferenceId::FP_REGISTER_TERM);
  }
  else if (k == Kind::FLOATINGPOINT_TO_REAL_TOTAL)
  {
    // Purify (fp.to_real x)
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node sk = sm->mkPurifySkolem(node);
    handleLemma(node.eqNode(sk), InferenceId::FP_REGISTER_TERM);
    d_abstractionMap.insert(sk, node);

    Node pd =
        nm->mkNode(Kind::IMPLIES,
                   nm->mkNode(Kind::OR,
                              nm->mkNode(Kind::FLOATINGPOINT_IS_NAN, node[0]),
                              nm->mkNode(Kind::FLOATINGPOINT_IS_INF, node[0])),
                   nm->mkNode(Kind::EQUAL, node, node[1]));
    handleLemma(pd, InferenceId::FP_REGISTER_TERM);

    Node z = nm->mkNode(
        Kind::IMPLIES,
        nm->mkNode(Kind::FLOATINGPOINT_IS_ZERO, node[0]),
        nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(Rational(0U))));
    handleLemma(z, InferenceId::FP_REGISTER_TERM);
    return;

    // TODO : bounds on the output from largest floats, #1914
  }
  else if (k == Kind::FLOATINGPOINT_TO_FP_FROM_REAL)
  {
    // Purify ((_ to_fp eb sb) rm x)
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node sk = sm->mkPurifySkolem(node);
    handleLemma(node.eqNode(sk), InferenceId::FP_REGISTER_TERM);
    d_abstractionMap.insert(sk, node);

    Node nnan =
        nm->mkNode(Kind::NOT, nm->mkNode(Kind::FLOATINGPOINT_IS_NAN, node));
    handleLemma(nnan, InferenceId::FP_REGISTER_TERM);

    Node z = nm->mkNode(
        Kind::IMPLIES,
        nm->mkNode(Kind::EQUAL, node[1], nm->mkConstReal(Rational(0U))),
        nm->mkNode(Kind::EQUAL,
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
      uint32_t exp_sz = tn.getFloatingPointExponentSize();
      uint32_t sig_sz = tn.getFloatingPointSignificandSize();
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
  Node lemma = rewrite(node);
  if (lemma != d_true)
  {
    /* We only send non-trivial lemmas. */
    d_im.lemma(lemma, id);
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
  d_invalidateModelCache = true;

  /* Resolve the abstractions for the conversion lemmas */
  if (level == EFFORT_LAST_CALL)
  {
    Trace("fp-abstraction")
        << "TheoryFp::check(): checking abstractions" << std::endl;
    TheoryModel* m = getValuation().getModel();
    for (const auto& [abstract, concrete] : d_abstractionMap)
    {
      Trace("fp-abstraction")
          << "TheoryFp::check(): Abstraction: " << abstract << std::endl;
      if (m->hasTerm(abstract))
      {  // Is actually used in the model
        Trace("fp-abstraction")
            << "TheoryFp::check(): ... relevant" << std::endl;
        refineAbstraction(m, abstract, concrete);
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

  if (atom.getKind() == Kind::EQUAL)
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

Node TheoryFp::getCandidateModelValue(TNode node)
{
  if (d_invalidateModelCache.get())
  {
    d_modelCache.clear();
  }
  d_invalidateModelCache.set(false);

  std::vector<TNode> visit;
  std::unordered_map<TNode, bool> visited;

  TNode cur;
  visit.push_back(node);
  do
  {
    cur = visit.back();
    visit.pop_back();

    auto it = d_modelCache.find(cur);
    if (it != d_modelCache.end() && !it->second.isNull())
    {
      continue;
    }

    auto vit = visited.find(cur);
    if (vit != visited.end() && vit->second)
    {
      continue;
    }

    if (cur.isConst())
    {
      d_modelCache[cur] = cur;
      visited[cur] = true;
      continue;
    }

    Node value;

    Kind kind = cur.getKind();
    if (kind == Kind::FLOATINGPOINT_TO_FP_FROM_SBV
        || kind == Kind::FLOATINGPOINT_TO_FP_FROM_UBV
        || kind == Kind::FLOATINGPOINT_TO_FP_FROM_REAL
        || kind == Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV
        || Theory::isLeafOf(cur, theory::THEORY_FP))
    {
      if (cur.getType().isFloatingPoint() || cur.getType().isRoundingMode())
      {
        value = d_wordBlaster->getValue(d_valuation, cur);
      }
      else
      {
        value = d_valuation.getCandidateModelValue(cur);
        if (value.isNull())
        {
          return value;
        }
      }
      d_modelCache[cur] = value;
      visited[cur] = true;
      continue;
    }

    if (vit == visited.end())
    {
      visit.push_back(cur);
      visited.emplace(cur, false);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (!vit->second)
    {
      NodeBuilder nb(kind);
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        nb << cur.getOperator();
      }

      std::unordered_map<Node, Node>::iterator iit;
      for (const TNode& child : cur)
      {
        iit = d_modelCache.find(child);
        Assert(iit != d_modelCache.end());
        Assert(!iit->second.isNull());
        nb << iit->second;
      }
      d_modelCache[cur] = rewrite(nb.constructNode());
      vit->second = true;
    }
  } while (!visit.empty());

  auto it = d_modelCache.find(node);
  Assert(it != d_modelCache.end());
  return it->second;
}

TrustNode TheoryFp::explain(TNode n)
{
  Trace("fp") << "TheoryFp::explain(): explain " << n << std::endl;

  // All things we assert directly (and not via bit-vector) should
  // come from the equality engine so this should be sufficient...
  std::vector<TNode> assumptions;

  bool polarity = n.getKind() != Kind::NOT;
  TNode atom = polarity ? n : n[0];
  if (atom.getKind() == Kind::EQUAL)
  {
    d_equalityEngine->explainEquality(atom[0], atom[1], polarity, assumptions);
  }
  else
  {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions);
  }

  Node exp = helper::buildConjunct(assumptions);
  return TrustNode::mkTrustPropExp(n, exp, nullptr);
}

EqualityStatus TheoryFp::getEqualityStatus(TNode a, TNode b)
{
  Node value_a = getCandidateModelValue(a);
  Node value_b = getCandidateModelValue(b);
  if (value_a.isNull() || value_b.isNull())
  {
    return EqualityStatus::EQUALITY_UNKNOWN;
  }
  if (value_a == value_b)
  {
    Trace("theory-fp") << EqualityStatus::EQUALITY_TRUE_IN_MODEL << std::endl;
    return EqualityStatus::EQUALITY_TRUE_IN_MODEL;
  }
  Trace("theory-fp") << EqualityStatus::EQUALITY_FALSE_IN_MODEL << std::endl;
  return EqualityStatus::EQUALITY_FALSE_IN_MODEL;
}

bool TheoryFp::collectModelInfo(TheoryModel* m,
                                const std::set<Node>& relevantTerms)
{
  // this override behavior to not assert equality engine
  return collectModelValues(m, relevantTerms);
}

bool TheoryFp::collectModelValues(TheoryModel* m,
                                  const std::set<Node>& termSet)
{
  Trace("fp-collectModelValues")
      << "TheoryFp::collectModelValues(): begin" << std::endl;
  if (TraceIsOn("fp-collectModelValues"))
  {
    for (std::set<Node>::const_iterator i(termSet.begin());
         i != termSet.end();
         ++i)
    {
      Trace("fp-collectModelValues")
          << "TheoryFp::collectModelValues(): termSet " << *i
          << std::endl;
    }
  }
  for (const Node& node : termSet)
  {
    TypeNode t = node.getType();
    if ((!t.isRoundingMode() && !t.isFloatingPoint()) || !this->isLeaf(node))
    {
      continue;
    }

    Trace("fp-collectModelValues")
        << "TheoryFp::collectModelValues(): " << node << std::endl;

    Node wordBlasted = d_wordBlaster->getValue(d_valuation, node);
    // We only assign the value if the FpWordBlaster actually has one, that is,
    // if FpWordBlaster::getValue() does not return a null node.
    if (!wordBlasted.isNull() && !m->assertEquality(node, wordBlasted, true))
    {
      Trace("fp-collectModelInfo")
          << "TheoryFp::collectModelValues(): ... not converted" << std::endl;
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
      Node compNaN = nm->mkNode(Kind::FLOATINGPOINT_COMPONENT_NAN, node);
      Node compInf = nm->mkNode(Kind::FLOATINGPOINT_COMPONENT_INF, node);
      Node compZero = nm->mkNode(Kind::FLOATINGPOINT_COMPONENT_ZERO, node);
      Node compExponent =
          nm->mkNode(Kind::FLOATINGPOINT_COMPONENT_EXPONENT, node);
      Node compSignificand =
          nm->mkNode(Kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND, node);

      eq::EqualityEngine* ee = m->getEqualityEngine();
      Assert(ee->hasTerm(compNaN));
      Assert(ee->hasTerm(compInf));
      Assert(ee->hasTerm(compZero));
      TNode rCompNaN = ee->getRepresentative(compNaN);
      TNode rCompInf = ee->getRepresentative(compInf);
      TNode rCompZero = ee->getRepresentative(compZero);
      Assert(rCompNaN.isConst());
      Assert(rCompInf.isConst());
      Assert(rCompZero.isConst());

      Assert(ee->hasTerm(compExponent)
             && ee->getRepresentative(compExponent).isConst());
      Assert(ee->hasTerm(compSignificand));
      Assert(ee->getRepresentative(compSignificand).isConst());

      // At most one of the flags (NaN, inf, zero) can be set
      Node one = nm->mkConst(BitVector(1U, 1U));
      Assert((rCompNaN == one ? 1 : 0) + (rCompInf == one ? 1 : 0)
                 + (rCompZero == one ? 1 : 0)
             <= 1);
    }
  }

  return true;
}

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
