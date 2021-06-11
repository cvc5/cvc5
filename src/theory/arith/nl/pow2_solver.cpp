/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Makai Mann, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of pow2 solver.
 */

#include "theory/arith/nl/pow2_solver.h"

#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

Pow2Solver::Pow2Solver(InferenceManager& im, ArithState& state, NlModel& model)
    : d_im(im), d_model(model), d_initRefine(state.getUserContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_two = nm->mkConst(Rational(2));
}

Pow2Solver::~Pow2Solver() {}

void Pow2Solver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_pow2s.clear();

  Trace("pow2-mv") << "POW2 terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != POW2)
    {
      // don't care about other terms
      continue;
    }
    d_pow2s.push_back(a);
  }

  Trace("pow2") << "We have " << d_pow2s.size() << " pow2 terms." << std::endl;
}

void Pow2Solver::checkInitialRefine()
{
}

void Pow2Solver::checkFullRefine()
{
}

Node Pow2Solver::valueBasedLemma(Node i)
{
	return Node();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
