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

#include "theory/arith/liastar/liastar_extension.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
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
  Trace("liastar-assert") << "Getting assertions..." << std::endl;
  Valuation v = d_arith.getValuation();
  std::cout << v.needCheck() << std::endl;
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("liastar-assert") << "Adding " << lit << std::endl;
    assertions.push_back(lit);
  }
  Trace("liastar-assert") << "...keep " << assertions.size() << " / "
                          << d_arith.numAssertions() << " assertions."
                          << std::endl;
}

std::vector<Node> LiaStarExtension::getUnsatisfiedAssertions(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (const auto& lit : assertions)
  {
    Trace("liastar-assert-false") << lit << std::endl;
  }
  return false_asserts;
}

void LiaStarExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                       const std::set<Node>& termSet)
{
  // run a last call effort check
  Trace("nl-ext") << "interceptModel: do model-based refinement" << std::endl;
  Result::Status res = modelBasedRefinement(termSet);
  if (res == Result::SAT)
  {
    Trace("nl-ext") << "interceptModel: do model repair" << std::endl;
    // modify the model values
  }
}

Result::Status LiaStarExtension::modelBasedRefinement(
    const std::set<Node>& termSet)
{
  d_checkCounter++;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("liastar-assert") << "Getting model values... check for [model-false]"
                          << std::endl;
  // get the assertions that are false in the model
  const std::vector<Node> false_asserts = getUnsatisfiedAssertions(assertions);
  Trace("liastar-assert") << "# false asserts = " << false_asserts.size()
                          << std::endl;

  // get the extended terms belonging to this theory
  std::vector<Node> xtsAll;
  d_extTheory.getTerms(xtsAll);
  // only consider those that are currently relevant based on the current
  // assertions, i.e. those contained in termSet
  std::vector<Node> xts;
  for (const Node& x : xtsAll)
  {
    if (termSet.find(x) != termSet.end())
    {
      xts.push_back(x);
    }
  }

  if (TraceIsOn("liastar-assert"))
  {
    Trace("liastar-assert")
        << "  processing LiaStarExtension::check : " << std::endl;
    Trace("liastar-assert")
        << "     " << false_asserts.size() << " false assertions" << std::endl;
    Trace("liastar-assert")
        << "     " << xts.size() << " extended terms: " << std::endl;
    Trace("liastar-assert") << "       ";
    for (unsigned j = 0; j < xts.size(); j++)
    {
      Trace("liastar-assert") << xts[j] << " ";
    }
    Trace("liastar-assert") << std::endl;
  }

  // did not add lemmas
  return Result::SAT;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
