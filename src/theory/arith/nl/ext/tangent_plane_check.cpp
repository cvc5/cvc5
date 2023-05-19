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
 * Implementation of tangent_plane check.
 */

#include "theory/arith/nl/ext/tangent_plane_check.h"

#include "expr/node.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/ext_state.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

TangentPlaneCheck::TangentPlaneCheck(Env& env, ExtState* data)
    : EnvObj(env), d_data(data)
{
}

void TangentPlaneCheck::check(bool asWaitingLemmas)
{
  Trace("nl-ext") << "Get monomial tangent plane lemmas..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  const std::map<Node, std::vector<Node> >& ccMap =
      d_data->d_mdb.getContainsChildrenMap();
  unsigned kstart = d_data->d_ms_vars.size();
  for (unsigned k = kstart; k < d_data->d_mterms.size(); k++)
  {
    Node t = d_data->d_mterms[k];
    // if this term requires a refinement
    if (d_data->d_tplane_refine.find(t) == d_data->d_tplane_refine.end())
    {
      continue;
    }
    Trace("nl-ext-tplanes")
        << "Look at monomial requiring refinement : " << t << std::endl;
    // get a decomposition
    std::map<Node, std::vector<Node> >::const_iterator it = ccMap.find(t);
    if (it == ccMap.end())
    {
      continue;
    }
    std::map<Node, std::map<Node, bool> > dproc;
    for (unsigned j = 0; j < it->second.size(); j++)
    {
      Node tc = it->second[j];
      Node one = mkOne(tc.getType());
      if (tc != one)
      {
        Node tc_diff = d_data->d_mdb.getContainsDiffNl(tc, t);
        Assert(!tc_diff.isNull());
        Node a = tc < tc_diff ? tc : tc_diff;
        Node b = tc < tc_diff ? tc_diff : tc;
        if (dproc[a].find(b) == dproc[a].end())
        {
          dproc[a][b] = true;
          Trace("nl-ext-tplanes")
              << "  decomposable into : " << a << " * " << b << std::endl;
          Node a_v_c = d_data->d_model.computeAbstractModelValue(a);
          Node b_v_c = d_data->d_model.computeAbstractModelValue(b);
          // points we will add tangent planes for
          std::vector<Node> pts[2];
          pts[0].push_back(a_v_c);
          pts[1].push_back(b_v_c);
          // if previously refined
          bool prevRefine = d_tangent_val_bound[0][a].find(b)
                            != d_tangent_val_bound[0][a].end();
          // a_min, a_max, b_min, b_max
          for (unsigned p = 0; p < 4; p++)
          {
            Node curr_v = p <= 1 ? a_v_c : b_v_c;
            if (prevRefine)
            {
              Node pt_v = d_tangent_val_bound[p][a][b];
              Assert(!pt_v.isNull());
              if (curr_v != pt_v)
              {
                Node do_extend = nm->mkNode(
                    (p == 1 || p == 3) ? Kind::GT : Kind::LT, curr_v, pt_v);
                do_extend = rewrite(do_extend);
                if (do_extend == d_data->d_true)
                {
                  for (unsigned q = 0; q < 2; q++)
                  {
                    pts[p <= 1 ? 0 : 1].push_back(curr_v);
                    pts[p <= 1 ? 1 : 0].push_back(
                        d_tangent_val_bound[p <= 1 ? 2 + q : q][a][b]);
                  }
                }
              }
            }
            else
            {
              d_tangent_val_bound[p][a][b] = curr_v;
            }
          }

          for (unsigned p = 0; p < pts[0].size(); p++)
          {
            Node a_v = pts[0][p];
            Node b_v = pts[1][p];

            // tangent plane
            Node tplane = nm->mkNode(Kind::SUB,
                                     nm->mkNode(Kind::ADD,
                                                nm->mkNode(Kind::MULT, b_v, a),
                                                nm->mkNode(Kind::MULT, a_v, b)),
                                     nm->mkNode(Kind::MULT, a_v, b_v));
            // construct the following lemmas:
            // t <= tplane  <=>  ((a <= a_v ^ b >= b_v) v (a >= a_v ^ b <= b_v))
            // t >= tplane  <=>  ((a <= a_v ^ b <= b_v) v (a >= a_v ^ b >= b_v))

            for (unsigned d = 0; d < 2; d++)
            {
              Node b1 = nm->mkNode(d == 0 ? Kind::GEQ : Kind::LEQ, b, b_v);
              Node b2 = nm->mkNode(d == 0 ? Kind::LEQ : Kind::GEQ, b, b_v);
              Node tlem = nm->mkNode(
                  Kind::EQUAL,
                  nm->mkNode(d == 0 ? Kind::LEQ : Kind::GEQ, t, tplane),
                  nm->mkNode(
                      Kind::OR,
                      nm->mkNode(Kind::AND, nm->mkNode(Kind::LEQ, a, a_v), b1),
                      nm->mkNode(
                          Kind::AND, nm->mkNode(Kind::GEQ, a, a_v), b2)));
              Trace("nl-ext-tplanes")
                  << "Tangent plane lemma : " << tlem << std::endl;
              CDProof* proof = nullptr;
              if (d_data->isProofEnabled())
              {
                proof = d_data->getProof();
                proof->addStep(tlem,
                               PfRule::ARITH_MULT_TANGENT,
                               {},
                               {t,
                                a,
                                b,
                                a_v,
                                b_v,
                                nm->mkConstReal(Rational(d == 0 ? -1 : 1))});
              }
              d_data->d_im.addPendingLemma(tlem,
                                           InferenceId::ARITH_NL_TANGENT_PLANE,
                                           proof,
                                           asWaitingLemmas);
            }
          }
        }
      }
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
