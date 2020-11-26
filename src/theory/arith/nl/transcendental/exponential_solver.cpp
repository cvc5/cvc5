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

void ExponentialSolver::checkMonotonic()
{
  Trace("nl-ext") << "Get monotonicity lemmas for transcendental functions..."
                  << std::endl;

  auto it = d_data->d_funcMap.find(Kind::EXPONENTIAL);
  if (it == d_data->d_funcMap.end())
  {
    Trace("nl-ext-exp") << "No exponential terms" << std::endl;
    return;
  }

  // sort arguments of all transcendentals
  std::vector<Node> tf_args;
  std::map<Node, Node> tf_arg_to_term;

  for (const Node& tf : it->second)
  {
    Node a = tf[0];
    Node mvaa = d_data->d_model.computeAbstractModelValue(a);
    if (mvaa.isConst())
    {
      Trace("nl-ext-exp") << "...tf term : " << a << std::endl;
      tf_args.push_back(a);
      tf_arg_to_term[a] = tf;
    }
  }

  if (tf_args.empty())
  {
    return;
  }

  sortByNlModel(
      tf_args.begin(), tf_args.end(), &d_data->d_model, true, false, true);

  Node targ, targval, t, tval;
  for (const auto& sarg : tf_args)
  {
    Node sargval = d_data->d_model.computeAbstractModelValue(sarg);
    Assert(sargval.isConst());
    Node s = tf_arg_to_term[sarg];
    Node sval = d_data->d_model.computeAbstractModelValue(s);
    Assert(sval.isConst());

    // store the concavity region
    d_data->d_tf_region[s] = 1;
    Trace("nl-ext-concavity") << ", arg model value = " << sargval << std::endl;

    if (!tval.isNull() && sval.getConst<Rational>() > tval.getConst<Rational>())
    {
      NodeManager* nm = NodeManager::currentNM();
      Node mono_lem = nm->mkNode(Kind::IMPLIES,
                                 nm->mkNode(Kind::GEQ, targ, sarg),
                                 nm->mkNode(Kind::GEQ, t, s));
      Trace("nl-ext-exp") << "Monotonicity lemma : " << mono_lem << std::endl;

      d_data->d_im.addPendingArithLemma(mono_lem,
                                        InferenceId::NL_T_MONOTONICITY);
    }
    // store the previous values
    targ = sarg;
    targval = sargval;
    t = s;
    tval = sval;
  }
}

void ExponentialSolver::doTangentLemma(TNode e, TNode c, TNode poly_approx)
{
  NodeManager* nm = NodeManager::currentNM();
  // compute tangent plane
  // Figure 3: T( x )
  // We use zero slope tangent planes, since the concavity of the Taylor
  // approximation cannot be easily established.
  // Tangent plane is valid in the interval [c,u).
  Node lem = nm->mkNode(Kind::IMPLIES,
                        nm->mkNode(Kind::GEQ, e[0], c),
                        nm->mkNode(Kind::GEQ, e, poly_approx));
  Trace("nl-ext-exp") << "*** Tangent plane lemma (pre-rewrite): " << lem
                      << std::endl;
  lem = Rewriter::rewrite(lem);
  Trace("nl-ext-exp") << "*** Tangent plane lemma : " << lem << std::endl;
  Assert(d_data->d_model.computeAbstractModelValue(lem) == d_data->d_false);
  // Figure 3 : line 9
  d_data->d_im.addPendingArithLemma(lem, InferenceId::NL_T_TANGENT, nullptr, true);
}

void ExponentialSolver::doSecantLemmas(
    TNode e, TNode poly_approx, TNode c, TNode poly_approx_c, unsigned d)
{
  d_data->doSecantLemmas(
      getSecantBounds(e, c, d), poly_approx, c, poly_approx_c, e, d, 1);
}

std::pair<Node, Node> ExponentialSolver::getSecantBounds(TNode e,
                                                         TNode c,
                                                         unsigned d)
{
  std::pair<Node, Node> bounds = d_data->getClosestSecantPoints(e, c, d);

  // Check if we already have neighboring secant points
  if (bounds.first.isNull())
  {
    // pick c-1
    bounds.first = Rewriter::rewrite(
        NodeManager::currentNM()->mkNode(Kind::MINUS, c, d_data->d_one));
  }
  if (bounds.second.isNull())
  {
    // pick c+1
    bounds.second = Rewriter::rewrite(
        NodeManager::currentNM()->mkNode(Kind::PLUS, c, d_data->d_one));
  }
  return bounds;
}

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
