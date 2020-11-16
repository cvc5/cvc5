/*********************                                                        */
/*! \file transcendental_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of solver for handling transcendental functions.
 **/

#include "theory/arith/nl/transcendental/exponential_solver.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

ExponentialSolver::ExponentialSolver(TranscendentalState* tstate)
    : d_data(tstate)
{
}

ExponentialSolver::~ExponentialSolver() {}

void ExponentialSolver::checkInitialRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext")
      << "Get initial refinement lemmas for transcendental functions..."
      << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    if (tfl.first != Kind::EXPONENTIAL)
    {
      continue;
    }
    Assert(tfl.first == Kind::EXPONENTIAL);
    for (const Node& t : tfl.second)
    {
      // initial refinements
      if (d_tf_initial_refine.find(t) == d_tf_initial_refine.end())
      {
        d_tf_initial_refine[t] = true;
        Node lem;
        // ( exp(x) > 0 ) ^ ( x=0 <=> exp( x ) = 1 ) ^ ( x < 0 <=> exp( x ) <
        // 1 ) ^ ( x <= 0 V exp( x ) > x + 1 )
        lem = nm->mkNode(
            Kind::AND,
            nm->mkNode(Kind::GT, t, d_data->d_zero),
            nm->mkNode(Kind::EQUAL,
                       t[0].eqNode(d_data->d_zero),
                       t.eqNode(d_data->d_one)),
            nm->mkNode(Kind::EQUAL,
                       nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                       nm->mkNode(Kind::LT, t, d_data->d_one)),
            nm->mkNode(
                Kind::OR,
                nm->mkNode(Kind::LEQ, t[0], d_data->d_zero),
                nm->mkNode(
                    Kind::GT, t, nm->mkNode(Kind::PLUS, t[0], d_data->d_one))));
        if (!lem.isNull())
        {
          d_data->d_im.addPendingArithLemma(lem, InferenceId::NL_T_INIT_REFINE);
        }
      }
    }
  }
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
