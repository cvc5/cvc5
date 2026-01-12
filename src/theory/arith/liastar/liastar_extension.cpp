/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Extension to the theory of arithmetic handling lia star operator.
 */

#include "liastar_extension.h"

#include "liastar_utils.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/evaluator.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

LiaStarExtension::LiaStarExtension(Env& env, TheoryArith& containing)
    : EnvObj(env),
      d_arith(containing),
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_checkCounter(0),
      d_extTheoryCb(d_astate.getEqualityEngine()),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasLiaStarTerms(context(), false)
{
  d_extTheory.addFunctionKind(Kind::STAR_CONTAINS);
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  d_zero = nodeManager()->mkConstInt(Rational(0));
}

LiaStarExtension::~LiaStarExtension() {}

void LiaStarExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-dependent simplification.
  if (d_extTheory.hasFunctionKind(n.getKind()))
  {
    d_hasLiaStarTerms = true;
    d_extTheory.registerTerm(n);
  }
}

void LiaStarExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("liastar-ext") << "Getting assertions..." << std::endl;
  Trace("liastar-ext") << "---------------------" << std::endl;
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("liastar-ext") << lit << std::endl;
    if (lit.getKind() == Kind::STAR_CONTAINS)
    {
      // for now, we only care about positive poalrity of star-contains
      assertions.push_back(lit);
    }
  }
  Trace("liastar-ext") << "---------------------" << std::endl;
  Trace("liastar-ext") << "...keep " << assertions.size() << " / "
                       << d_arith.numAssertions() << " assertions."
                       << std::endl;
}

void LiaStarExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                       const std::set<Node>& termSet)
{
  // run a last call effort check
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;
  d_checkCounter++;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const auto& literal : assertions)
  {
    Assert(literal.getKind() == Kind::STAR_CONTAINS);
    Node vec = literal[2];
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(literal, nm);
    // assert that vector elements are non negative
    d_im.addPendingLemma(nonnegative, InferenceId::ARITH_LIA_STAR);
    // add a spliting lemma for vector predicate

    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    d_im.addPendingLemma(split, InferenceId::ARITH_LIA_STAR);
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
    std::vector<Node> keys;
    std::vector<Node> values;

    for (const auto& [key, value] : arithModel)
    {
      keys.push_back(key);
      values.push_back(value);
    }

    Node value = vectorPredicate.substitute(
        keys.begin(), keys.end(), values.begin(), values.end());
    value = rewrite(value);

    // Node vectorValue = literal[2].substitute(
    //     keys.begin(), keys.end(), values.begin(), values.end());
    std::vector<Node> elements;
    Node vectorValue;
    if (literal[2].isConst())
    {
      vectorValue = literal[2];
    }
    else
    {
      Trace("liastar-ext-debug") << "value: " << value << std::endl;
      Trace("liastar-ext-debug") << "vector value of: " << literal[2] << " is "
                                 << vectorValue << std::endl;
      for (size_t i = 0; i < literal[2].getType().getTupleLength(); i++)
      {
        Node eValue = datatypes::TupleUtils::nthElementOfTuple(literal[2], i);
        Trace("liastar-ext-debug") << "eValue: " << eValue << std::endl;
        if (eValue.isConst())
        {
          elements.push_back(eValue);
        }
        else
        {
          Node modelValue = arithModel[eValue];
          Trace("liastar-ext-debug")
              << "modelValue: " << modelValue << std::endl;
          elements.push_back(modelValue);
        }
      }
      vectorValue = datatypes::TupleUtils::constructTupleFromElements(
          literal[2].getType(),
          elements,
          0,
          literal[2].getType().getTupleLength() - 1);
      vectorValue = rewrite(vectorValue);
    }
    Trace("liastar-ext-debug") << "value: " << value << std::endl;
    Trace("liastar-ext-debug") << "vector value of: " << literal[2] << " is "
                               << vectorValue << std::endl;
    Node v = literal[2];
    if (value == d_true)
    {
      Trace("liastar-ext-debug")
          << "----------------------------------------" << std::endl;
      Trace("liastar-ext-debug") << literal << std::endl;
      Trace("liastar-ext-debug")
          << "----------------------------------------" << std::endl;
      d_processedVectors.push_back(v);
      return;
    }
    else  //(value == d_false)
    {
      // the candidate model does not satisfy the star predicate.
      // This does not mean the vector is not a member of the star set,
      // because it could be a linear combinations of other vectors in the set.
      // But we don't know them at this point.
      // So to make progress, we split on whether the vector before evaluation,
      // which may contain variables, satisfies the predicate or not.
      // So if we have
      // (star-contains ((x1 ... x_n) (p x1 ... x_n) (tuple y1 ... y_n)))
      // we add the lemma
      // (or (p y1 ... y_n) (not (p y1 ... y_n)) hoping that
      // (p y1 ... y_n) holds to force LIA solver to find a model.
      // If not, then we need to work harder with (not (p y1 ... y_n))
      // to find a linear combination of vectors if it is satisfiable.

      Node lemma =
          nm->mkNode(Kind::OR, vectorPredicate, vectorPredicate.negate());
      d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR);
      Trace("liastar-ext") << "lemma = " << lemma << std::endl;
      if (d_im.hasPendingLemma())
      {
        Trace("liastar-ext") << "has not sent the lemma before" << std::endl;
      }
      else
      {
        Trace("liastar-ext") << "has already sent the lemma" << std::endl;
        // more work need to be done
        if (std::find(d_processedVectors.begin(), d_processedVectors.end(), v)
            != d_processedVectors.end())
        {
          Trace("liastar-ext") << "already processed vector " << v << std::endl;
          continue;
        }
        Node v1 = nm->getSkolemManager()->mkDummySkolem("v1", v.getType());
        Node v2 = nm->getSkolemManager()->mkDummySkolem("v2", v.getType());

        auto size = v1.getType().getTupleTypes().size();

        for (size_t i = 0; i < size; i++)
        {
          Node v_i = datatypes::TupleUtils::nthElementOfTuple(v, i);
          Node v1_i = datatypes::TupleUtils::nthElementOfTuple(v1, i);
          Node v2_i = datatypes::TupleUtils::nthElementOfTuple(v2, i);
          Node plus = nm->mkNode(Kind::ADD, v1_i, v2_i);
          Node constraint = v_i.eqNode(plus);
          d_im.addPendingLemma(constraint, InferenceId::ARITH_LIA_STAR);
          Trace("liastar-ext")
              << "Added constraint:  " << constraint << std::endl;
        }

        Node v1Literal =
            nm->mkNode(Kind::STAR_CONTAINS, literal[0], literal[1], v1);
        Node v2Literal =
            nm->mkNode(Kind::STAR_CONTAINS, literal[0], literal[1], v2);
        d_im.addPendingLemma(v1Literal, InferenceId::ARITH_LIA_STAR);
        d_im.addPendingLemma(v2Literal, InferenceId::ARITH_LIA_STAR);
        d_im.addPendingLemma(isNotZeroVector(v1), InferenceId::ARITH_LIA_STAR);
        d_im.addPendingLemma(isNotZeroVector(v2), InferenceId::ARITH_LIA_STAR);
        Trace("liastar-ext") << "Add v1:  " << v1Literal << std::endl;
        Trace("liastar-ext") << "Add v2:  " << v2Literal << std::endl;
        d_processedVectors.push_back(v);
        d_im.doPendingLemmas();
      }
    }
  }
}

Node LiaStarExtension::isNotZeroVector(Node v)
{
  std::vector<Node> elements = datatypes::TupleUtils::getTupleElements(v);
  Node notZero = d_false;
  for (Node element : elements)
  {
    notZero = notZero.orNode(element.eqNode(d_zero).notNode());
  }
  Trace("liastar-ext") << v << " is not zero: " << notZero << std::endl;
  return notZero;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
