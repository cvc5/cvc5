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

#include "theory/arith/nl/transcendental/sine_solver.h"

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

SineSolver::SineSolver(TranscendentalState* tstate) : d_data(tstate) {}

SineSolver::~SineSolver() {}

void SineSolver::checkInitialRefine()
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext")
      << "Get initial refinement lemmas for transcendental functions..."
      << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    if (tfl.first != Kind::SINE)
    {
      continue;
    }
    for (const Node& t : tfl.second)
    {
      // initial refinements
      if (d_tf_initial_refine.find(t) == d_tf_initial_refine.end())
      {
        d_tf_initial_refine[t] = true;
        Node lem;
        Node symn = nm->mkNode(Kind::SINE,
                               nm->mkNode(Kind::MULT, d_data->d_neg_one, t[0]));
        symn = Rewriter::rewrite(symn);
        // Can assume it is its own master since phase is split over 0,
        // hence  -pi <= t[0] <= pi implies -pi <= -t[0] <= pi.
        d_data->d_trMaster[symn] = symn;
        d_data->d_trSlaves[symn].insert(symn);
        Assert(d_data->d_trSlaves.find(t) != d_data->d_trSlaves.end());
        std::vector<Node> children;

        lem =
            nm->mkNode(Kind::AND,
                       // bounds
                       nm->mkNode(Kind::AND,
                                  nm->mkNode(Kind::LEQ, t, d_data->d_one),
                                  nm->mkNode(Kind::GEQ, t, d_data->d_neg_one)),
                       // symmetry
                       nm->mkNode(Kind::PLUS, t, symn).eqNode(d_data->d_zero),
                       // sign
                       nm->mkNode(Kind::EQUAL,
                                  nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::LT, t, d_data->d_zero)),
                       // zero val
                       nm->mkNode(Kind::EQUAL,
                                  nm->mkNode(Kind::GT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::GT, t, d_data->d_zero)));
        lem = nm->mkNode(
            Kind::AND,
            lem,
            // zero tangent
            nm->mkNode(Kind::AND,
                       nm->mkNode(Kind::IMPLIES,
                                  nm->mkNode(Kind::GT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::LT, t, t[0])),
                       nm->mkNode(Kind::IMPLIES,
                                  nm->mkNode(Kind::LT, t[0], d_data->d_zero),
                                  nm->mkNode(Kind::GT, t, t[0]))),
            // pi tangent
            nm->mkNode(
                Kind::AND,
                nm->mkNode(
                    Kind::IMPLIES,
                    nm->mkNode(Kind::LT, t[0], d_data->d_pi),
                    nm->mkNode(Kind::LT,
                               t,
                               nm->mkNode(Kind::MINUS, d_data->d_pi, t[0]))),
                nm->mkNode(
                    Kind::IMPLIES,
                    nm->mkNode(Kind::GT, t[0], d_data->d_pi_neg),
                    nm->mkNode(
                        Kind::GT,
                        t,
                        nm->mkNode(Kind::MINUS, d_data->d_pi_neg, t[0])))));
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
