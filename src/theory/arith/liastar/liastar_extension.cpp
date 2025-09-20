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
  Valuation v = d_arith.getValuation();
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    if (lit.getKind() == Kind::STAR_CONTAINS)
    {
      // for now, we only care about positive poalrity of star-contains
      Trace("liastar-ext") << "Adding " << lit << std::endl;
      assertions.push_back(lit);
    }
  }
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
  // get the assertions that are false in the model
  const std::vector<Node> unsatisfied;
  for (const auto& literal : assertions)
  {
    Assert(literal.getKind() == Kind::STAR_CONTAINS);
    Node vectorPredicate = LiaStarUtils::getVectorPredicate(literal);
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

    Trace("liastar-ext-debug") << "value: " << value << std::endl;
    if (value == d_false)
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
      NodeManager* nm = nodeManager();
      Node lemma =
          nm->mkNode(Kind::OR, vectorPredicate, vectorPredicate.negate());
      d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR);
      Trace("liastar-ext") << "lemma = " << lemma << std::endl;
    }
  }
  Trace("liastar-ext") << "unsatisfied = " << unsatisfied.size() << std::endl;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
