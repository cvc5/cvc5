/*********************                                                        */
/*! \file tangent_plane_check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of tangent_plane check
 **/

#include "theory/arith/nl/ext/tangent_plane_check.h"

#include "expr/node.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

TangentPlaneCheck::TangentPlaneCheck(ExtState* data) : d_data(data) {}

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
      if (tc != d_data->d_one)
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
                do_extend = Rewriter::rewrite(do_extend);
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
            Node tplane = nm->mkNode(Kind::MINUS,
                                     nm->mkNode(Kind::PLUS,
                                                nm->mkNode(Kind::MULT, b_v, a),
                                                nm->mkNode(Kind::MULT, a_v, b)),
                                     nm->mkNode(Kind::MULT, a_v, b_v));
            // conjuncts of the tangent plane lemma
            std::vector<Node> tplaneConj;
            for (unsigned d = 0; d < 4; d++)
            {
              Node aa =
                  nm->mkNode(d == 0 || d == 3 ? Kind::GEQ : Kind::LEQ, a, a_v);
              Node ab =
                  nm->mkNode(d == 1 || d == 3 ? Kind::GEQ : Kind::LEQ, b, b_v);
              Node conc = nm->mkNode(d <= 1 ? Kind::LEQ : Kind::GEQ, t, tplane);
              Node tlem = nm->mkNode(Kind::OR, aa.negate(), ab.negate(), conc);
              Trace("nl-ext-tplanes")
                  << "Tangent plane lemma : " << tlem << std::endl;
              tplaneConj.push_back(tlem);
            }

            // tangent plane reverse implication

            // t <= tplane -> ( (a <= a_v ^ b >= b_v) v
            // (a >= a_v ^ b <= b_v) ).
            // in clause form, the above becomes
            // t <= tplane -> a <= a_v v b <= b_v.
            // t <= tplane -> b >= b_v v a >= a_v.
            Node a_leq_av = nm->mkNode(Kind::LEQ, a, a_v);
            Node b_leq_bv = nm->mkNode(Kind::LEQ, b, b_v);
            Node a_geq_av = nm->mkNode(Kind::GEQ, a, a_v);
            Node b_geq_bv = nm->mkNode(Kind::GEQ, b, b_v);

            Node t_leq_tplane = nm->mkNode(Kind::LEQ, t, tplane);
            Node a_leq_av_or_b_leq_bv =
                nm->mkNode(Kind::OR, a_leq_av, b_leq_bv);
            Node b_geq_bv_or_a_geq_av =
                nm->mkNode(Kind::OR, b_geq_bv, a_geq_av);
            Node ub_reverse1 = nm->mkNode(
                Kind::OR, t_leq_tplane.negate(), a_leq_av_or_b_leq_bv);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << ub_reverse1
                << std::endl;
            tplaneConj.push_back(ub_reverse1);
            Node ub_reverse2 = nm->mkNode(
                Kind::OR, t_leq_tplane.negate(), b_geq_bv_or_a_geq_av);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << ub_reverse2
                << std::endl;
            tplaneConj.push_back(ub_reverse2);

            // t >= tplane -> ( (a <= a_v ^ b <= b_v) v
            // (a >= a_v ^ b >= b_v) ).
            // in clause form, the above becomes
            // t >= tplane -> a <= a_v v b >= b_v.
            // t >= tplane -> b >= b_v v a <= a_v
            Node t_geq_tplane = nm->mkNode(Kind::GEQ, t, tplane);
            Node a_leq_av_or_b_geq_bv =
                nm->mkNode(Kind::OR, a_leq_av, b_geq_bv);
            Node a_geq_av_or_b_leq_bv =
                nm->mkNode(Kind::OR, a_geq_av, b_leq_bv);
            Node lb_reverse1 = nm->mkNode(
                Kind::OR, t_geq_tplane.negate(), a_leq_av_or_b_geq_bv);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << lb_reverse1
                << std::endl;
            tplaneConj.push_back(lb_reverse1);
            Node lb_reverse2 = nm->mkNode(
                Kind::OR, t_geq_tplane.negate(), a_geq_av_or_b_leq_bv);
            Trace("nl-ext-tplanes")
                << "Tangent plane lemma (reverse) : " << lb_reverse2
                << std::endl;
            tplaneConj.push_back(lb_reverse2);

            Node tlem = nm->mkAnd(tplaneConj);
            d_data->d_im.addPendingArithLemma(
                tlem, InferenceId::NL_TANGENT_PLANE, asWaitingLemmas);
          }
        }
      }
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4