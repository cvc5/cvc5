/******************************************************************************
 * Top contributors (to current version):
 *    Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of parametric integer and (PIAND) solver.
 */

#include "theory/arith/nl/piand_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

PIAndSolver::PIAndSolver(Env& env, InferenceManager& im, NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_iandUtils(env.getNodeManager()),
      d_initRefine(userContext())
{
  NodeManager* nm = nodeManager();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

PIAndSolver::~PIAndSolver() {}

void PIAndSolver::initLastCall(const std::vector<Node>& assertions,
                               const std::vector<Node>& false_asserts,
                               const std::vector<Node>& xts)
{
  d_piands.clear();

  Trace("piand-mv") << "PIAND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != Kind::PIAND)
    {
      // don't care about other terms
      continue;
    }
    d_piands[a[0]].push_back(a);
  }
  Trace("piand") << "We have " << d_piands.size() << " PIAND bit-width."
                 << std::endl;
}

void PIAndSolver::checkInitialRefine() {}

void PIAndSolver::checkFullRefine() {}

Node PIAndSolver::valueBasedLemma(Node i) { return i; }

Node PIAndSolver::sumBasedLemma(Node i, Kind kind) { return i; }

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
