/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common data shared by multiple checks.
 */

#include "theory/arith/nl/ext/ext_state.h"

#include <vector>

#include "expr/node.h"
#include "proof/proof.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/monomial.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ExtState::ExtState(Env& env, InferenceManager& im, NlModel& model)
    : EnvObj(env), d_im(im), d_model(model)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConstInt(Rational(-1));
  if (env.isTheoryProofProducing())
  {
    d_proof.reset(new CDProofSet<CDProof>(env, env.getUserContext(), "nl-ext"));
  }
}

void ExtState::init(const std::vector<Node>& xts)
{
  d_ms_vars.clear();
  d_ms.clear();
  d_mterms.clear();
  d_tplane_refine.clear();

  Trace("nl-ext-mv") << "Extended terms : " << std::endl;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    d_model.computeConcreteModelValue(a);
    d_model.computeAbstractModelValue(a);
    d_model.printModelValue("nl-ext-mv", a);
    Kind ak = a.getKind();
    if (ak == Kind::NONLINEAR_MULT)
    {
      d_ms.push_back(a);

      // context-independent registration
      d_mdb.registerMonomial(a);

      const std::vector<Node>& varList = d_mdb.getVariableList(a);
      for (const Node& v : varList)
      {
        if (std::find(d_ms_vars.begin(), d_ms_vars.end(), v) == d_ms_vars.end())
        {
          d_ms_vars.push_back(v);
        }
      }
      // mark processed if has a "one" factor (will look at reduced monomial)?
    }
  }

  // register constants
  d_mdb.registerMonomial(d_one);

  // register variables
  Trace("nl-ext-mv") << "Variables in monomials : " << std::endl;
  for (unsigned i = 0; i < d_ms_vars.size(); i++)
  {
    Node v = d_ms_vars[i];
    d_mdb.registerMonomial(v);
    d_model.computeConcreteModelValue(v);
    d_model.computeAbstractModelValue(v);
    d_model.printModelValue("nl-ext-mv", v);
  }

  Trace("nl-ext") << "We have " << d_ms.size() << " monomials." << std::endl;
}

bool ExtState::isProofEnabled() const { return d_proof.get() != nullptr; }

CDProof* ExtState::getProof()
{
  Assert(isProofEnabled());
  return d_proof->allocateProof(d_env.getUserContext());
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
