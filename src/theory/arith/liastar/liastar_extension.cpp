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
  std::cout << v.needCheck() << std::endl;
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
    Node variables = literal[0];
    Node predicate = literal[1];
    Node vec = literal[2];

    std::unordered_set<Node> boundVariables;
    for (const auto& v : variables)
    {
      boundVariables.insert(v);
    }
    std::vector<Node> vecElements =
        datatypes::TupleUtils::getTupleElements(vec);
    Node substitute = predicate.substitute(variables.begin(),
                                           variables.end(),
                                           vecElements.begin(),
                                           vecElements.end());
    std::vector<Node> keys;
    std::vector<Node> values;

    for (const auto& [key, value] : arithModel)
    {
      keys.push_back(key);
      values.push_back(value);
    }

    Node value = substitute.substitute(
        keys.begin(), keys.end(), values.begin(), values.end());
    value = rewrite(value);
    Trace("liastar-ext-debug") << "literal: " << literal << std::endl;
    Trace("liastar-ext-debug") << "predicate: " << predicate << std::endl;
    Trace("liastar-ext-debug") << "substitute: " << substitute << std::endl;
    Trace("liastar-ext-debug") << "value: " << value << std::endl;
    if (value == d_false)
    {
      d_im.addPendingLemma(substitute, InferenceId::ARITH_LIA_STAR);
    }
  }
  Trace("liastar-ext") << "unsatisfied = " << unsatisfied.size() << std::endl;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
