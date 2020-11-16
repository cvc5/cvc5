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

  // sort arguments of all transcendentals
  std::map<Kind, std::vector<Node> > sorted_tf_args;
  std::map<Kind, std::map<Node, Node> > tf_arg_to_term;

  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    Kind k = tfl.first;
    if (tfl.first != Kind::EXPONENTIAL)
    {
      continue;
    }
    for (const Node& tf : tfl.second)
    {
      Node a = tf[0];
      Node mvaa = d_data->d_model.computeAbstractModelValue(a);
      if (mvaa.isConst())
      {
        Trace("nl-ext-tf-mono-debug") << "...tf term : " << a << std::endl;
        sorted_tf_args[k].push_back(a);
        tf_arg_to_term[k][a] = tf;
      }
    }
  }

  SortNlModel smv;
  smv.d_nlm = &d_data->d_model;
  // sort by concrete values
  smv.d_isConcrete = true;
  smv.d_reverse_order = true;
  for (std::pair<const Kind, std::vector<Node> >& tfl : d_data->d_funcMap)
  {
    Kind k = tfl.first;
    if (tfl.first != Kind::EXPONENTIAL)
    {
      continue;
    }
    if (!sorted_tf_args[k].empty())
    {
      std::sort(sorted_tf_args[k].begin(), sorted_tf_args[k].end(), smv);
      Trace("nl-ext-tf-mono") << "Sorted transcendental function list for " << k
                              << " : " << std::endl;
      for (unsigned i = 0; i < sorted_tf_args[k].size(); i++)
      {
        Node targ = sorted_tf_args[k][i];
        Node mvatarg = d_data->d_model.computeAbstractModelValue(targ);
        Trace("nl-ext-tf-mono")
            << "  " << targ << " -> " << mvatarg << std::endl;
        Node t = tf_arg_to_term[k][targ];
        Node mvat = d_data->d_model.computeAbstractModelValue(t);
        Trace("nl-ext-tf-mono") << "     f-val : " << mvat << std::endl;
      }
      std::vector<Node> mpoints;
      std::vector<Node> mpoints_vals;
        mpoints.push_back(Node::null());
      if (!mpoints.empty())
      {
        // get model values for points
        for (unsigned i = 0; i < mpoints.size(); i++)
        {
          Node mpv;
          if (!mpoints[i].isNull())
          {
            mpv = d_data->d_model.computeAbstractModelValue(mpoints[i]);
            Assert(mpv.isConst());
          }
          mpoints_vals.push_back(mpv);
        }

        unsigned mdir_index = 0;
        int monotonic_dir = -1;
        Node mono_bounds[2];
        Node targ, targval, t, tval;
        for (unsigned i = 0, size = sorted_tf_args[k].size(); i < size; i++)
        {
          Node sarg = sorted_tf_args[k][i];
          Node sargval = d_data->d_model.computeAbstractModelValue(sarg);
          Assert(sargval.isConst());
          Node s = tf_arg_to_term[k][sarg];
          Node sval = d_data->d_model.computeAbstractModelValue(s);
          Assert(sval.isConst());

          // increment to the proper monotonicity region
          bool increment = true;
          while (increment && mdir_index < mpoints.size())
          {
            increment = false;
            if (mpoints[mdir_index].isNull())
            {
              increment = true;
            }
            else
            {
              Node pval = mpoints_vals[mdir_index];
              Assert(pval.isConst());
              if (sargval.getConst<Rational>() < pval.getConst<Rational>())
              {
                increment = true;
                Trace("nl-ext-tf-mono") << "...increment at " << sarg
                                        << " since model value is less than "
                                        << mpoints[mdir_index] << std::endl;
              }
            }
            if (increment)
            {
              tval = Node::null();
              mono_bounds[1] = mpoints[mdir_index];
              mdir_index++;
              monotonic_dir = regionToMonotonicityDir(mdir_index);
              if (mdir_index < mpoints.size())
              {
                mono_bounds[0] = mpoints[mdir_index];
              }
              else
              {
                mono_bounds[0] = Node::null();
              }
            }
          }
          // store the concavity region
          d_data->d_tf_region[s] = mdir_index;
          Trace("nl-ext-concavity") << "Transcendental function " << s
                                    << " is in region #" << mdir_index;
          Trace("nl-ext-concavity")
              << ", arg model value = " << sargval << std::endl;

          if (!tval.isNull())
          {
            NodeManager* nm = NodeManager::currentNM();
            Node mono_lem;
            if (monotonic_dir == 1
                && sval.getConst<Rational>() > tval.getConst<Rational>())
            {
              mono_lem = nm->mkNode(
                  Kind::IMPLIES, nm->mkNode(Kind::GEQ, targ, sarg), nm->mkNode(Kind::GEQ, t, s));
            }
            else if (monotonic_dir == -1
                     && sval.getConst<Rational>() < tval.getConst<Rational>())
            {
              mono_lem = nm->mkNode(
                  Kind::IMPLIES, nm->mkNode(Kind::LEQ, targ, sarg), nm->mkNode(Kind::LEQ, t, s));
            }
            if (!mono_lem.isNull())
            {
              if (!mono_bounds[0].isNull())
              {
                Assert(!mono_bounds[1].isNull());
                mono_lem = nm->mkNode(
                    Kind::IMPLIES,
                    nm->mkNode(Kind::AND,
                               mkBounded(mono_bounds[0], targ, mono_bounds[1]),
                               mkBounded(mono_bounds[0], sarg, mono_bounds[1])),
                    mono_lem);
              }
              Trace("nl-ext-tf-mono")
                  << "Monotonicity lemma : " << mono_lem << std::endl;

              d_data->d_im.addPendingArithLemma(mono_lem,
                                        InferenceId::NL_T_MONOTONICITY);
            }
          }
          // store the previous values
          targ = sarg;
          targval = sargval;
          t = s;
          tval = sval;
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
