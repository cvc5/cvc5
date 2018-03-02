/*********************                                                        */
/*! \file cegis.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cegis
 **/

#include "theory/quantifiers/sygus/cegis.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
// FIXME : remove these includes (github issue #1156)
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Cegis::Cegis(QuantifiersEngine* qe, CegConjecture* p) : SygusModule(qe, p) {}
bool Cegis::initialize(Node n,
                       const std::vector<Node>& candidates,
                       std::vector<Node>& lemmas)
{
  d_base_body = n;
  if (d_base_body.getKind() == NOT && d_base_body[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_body[0][0])
    {
      d_base_vars.push_back(v);
    }
    d_base_body = d_base_body[0][1];
  }

  // assign the cegis sampler if applicable
  if (options::cegisSample() != CEGIS_SAMPLE_NONE)
  {
    Trace("cegis-sample") << "Initialize sampler for " << d_base_body << "..."
                          << std::endl;
    TypeNode bt = d_base_body.getType();
    d_cegis_sampler.initialize(bt, d_base_vars, options::sygusSamples());
  }

  // initialize an enumerator for each candidate
  TermDbSygus* tds = d_qe->getTermDatabaseSygus();
  for (unsigned i = 0; i < candidates.size(); i++)
  {
    tds->registerEnumerator(candidates[i], candidates[i], d_parent);
  }
  return true;
}

void Cegis::getTermList(const std::vector<Node>& candidates,
                        std::vector<Node>& enums)
{
  enums.insert(enums.end(), candidates.begin(), candidates.end());
}

/** construct candidate */
bool Cegis::constructCandidates(const std::vector<Node>& enums,
                                const std::vector<Node>& enum_values,
                                const std::vector<Node>& candidates,
                                std::vector<Node>& candidate_values,
                                std::vector<Node>& lems)
{
  candidate_values.insert(
      candidate_values.end(), enum_values.begin(), enum_values.end());

  if (options::sygusDirectEval())
  {
    NodeManager* nm = NodeManager::currentNM();
    bool addedEvalLemmas = false;
    if (options::sygusCRefEval())
    {
      Trace("cegqi-engine") << "  *** Do conjecture refinement evaluation..."
                            << std::endl;
      // see if any refinement lemma is refuted by evaluation
      std::vector<Node> cre_lems;
      getRefinementEvalLemmas(candidates, candidate_values, cre_lems);
      if (!cre_lems.empty())
      {
        for (unsigned j = 0; j < cre_lems.size(); j++)
        {
          Node lem = cre_lems[j];
          if (d_qe->addLemma(lem))
          {
            Trace("cegqi-lemma") << "Cegqi::Lemma : cref evaluation : " << lem
                                 << std::endl;
            addedEvalLemmas = true;
          }
        }
        // we could, but do not return here.
        // experimentally, it is better to add the lemmas below as well,
        // in parallel.
      }
    }
    Trace("cegqi-engine") << "  *** Do direct evaluation..." << std::endl;
    std::vector<Node> eager_terms;
    std::vector<Node> eager_vals;
    std::vector<Node> eager_exps;
    TermDbSygus* tds = d_qe->getTermDatabaseSygus();
    for (unsigned j = 0, size = candidates.size(); j < size; j++)
    {
      Trace("cegqi-debug") << "  register " << candidates[j] << " -> "
                           << candidate_values[j] << std::endl;
      tds->registerModelValue(candidates[j],
                              candidate_values[j],
                              eager_terms,
                              eager_vals,
                              eager_exps);
    }
    Trace("cegqi-debug") << "...produced " << eager_terms.size()
                         << " eager evaluation lemmas." << std::endl;

    for (unsigned j = 0, size = eager_terms.size(); j < size; j++)
    {
      Node lem = nm->mkNode(kind::OR,
                            eager_exps[j].negate(),
                            eager_terms[j].eqNode(eager_vals[j]));
      if (d_qe->getTheoryEngine()->isTheoryEnabled(THEORY_BV))
      {
        // FIXME: hack to incorporate hacks from BV for division by zero
        // (github issue #1156)
        lem = bv::TheoryBVRewriter::eliminateBVSDiv(lem);
      }
      if (d_qe->addLemma(lem))
      {
        Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation : " << lem
                             << std::endl;
        addedEvalLemmas = true;
      }
    }
    if (addedEvalLemmas)
    {
      return false;
    }
  }

  return true;
}

void Cegis::registerRefinementLemma(const std::vector<Node>& vars,
                                    Node lem,
                                    std::vector<Node>& lems)
{
  d_refinement_lemmas.push_back(lem);
  // Make the refinement lemma and add it to lems.
  // This lemma is guarded by the parent's guard, which has the semantics
  // "this conjecture has a solution", hence this lemma states:
  // if the parent conjecture has a solution, it satisfies the specification
  // for the given concrete point.
  Node rlem =
      NodeManager::currentNM()->mkNode(OR, d_parent->getGuard().negate(), lem);
  lems.push_back(rlem);
}

void Cegis::getRefinementEvalLemmas(const std::vector<Node>& vs,
                                    const std::vector<Node>& ms,
                                    std::vector<Node>& lems)
{
  Trace("sygus-cref-eval") << "Cref eval : conjecture has "
                           << getNumRefinementLemmas() << " refinement lemmas."
                           << std::endl;
  unsigned nlemmas = getNumRefinementLemmas();
  if (nlemmas > 0 || options::cegisSample() != CEGIS_SAMPLE_NONE)
  {
    Assert(vs.size() == ms.size());

    TermDbSygus* tds = d_qe->getTermDatabaseSygus();
    NodeManager* nm = NodeManager::currentNM();

    Node nfalse = nm->mkConst(false);
    Node neg_guard = d_parent->getGuard().negate();
    for (unsigned i = 0; i <= nlemmas; i++)
    {
      if (i == nlemmas)
      {
        bool addedSample = false;
        // find a new one by sampling, if applicable
        if (options::cegisSample() != CEGIS_SAMPLE_NONE)
        {
          addedSample = sampleAddRefinementLemma(vs, ms, lems);
        }
        if (!addedSample)
        {
          return;
        }
      }
      Node lem;
      std::map<Node, Node> visited;
      std::map<Node, std::vector<Node> > exp;
      lem = getRefinementLemma(i);
      if (!lem.isNull())
      {
        std::vector<Node> lem_conj;
        // break into conjunctions
        if (lem.getKind() == kind::AND)
        {
          for (unsigned i = 0; i < lem.getNumChildren(); i++)
          {
            lem_conj.push_back(lem[i]);
          }
        }
        else
        {
          lem_conj.push_back(lem);
        }
        EvalSygusInvarianceTest vsit;
        for (unsigned j = 0; j < lem_conj.size(); j++)
        {
          Node lemc = lem_conj[j];
          Trace("sygus-cref-eval") << "Check refinement lemma conjunct " << lemc
                                   << " against current model." << std::endl;
          Trace("sygus-cref-eval2") << "Check refinement lemma conjunct "
                                    << lemc << " against current model."
                                    << std::endl;
          Node cre_lem;
          Node lemcs =
              lemc.substitute(vs.begin(), vs.end(), ms.begin(), ms.end());
          Trace("sygus-cref-eval2") << "...under substitution it is : " << lemcs
                                    << std::endl;
          Node lemcsu = vsit.doEvaluateWithUnfolding(tds, lemcs);
          Trace("sygus-cref-eval2") << "...after unfolding is : " << lemcsu
                                    << std::endl;
          if (lemcsu.isConst() && !lemcsu.getConst<bool>())
          {
            std::vector<Node> msu;
            std::vector<Node> mexp;
            msu.insert(msu.end(), ms.begin(), ms.end());
            for (unsigned k = 0; k < vs.size(); k++)
            {
              vsit.setUpdatedTerm(msu[k]);
              msu[k] = vs[k];
              // substitute for everything except this
              Node sconj =
                  lemc.substitute(vs.begin(), vs.end(), msu.begin(), msu.end());
              vsit.init(sconj, vs[k], nfalse);
              // get minimal explanation for this
              Node ut = vsit.getUpdatedTerm();
              Trace("sygus-cref-eval2-debug")
                  << "  compute min explain of : " << vs[k] << " = " << ut
                  << std::endl;
              tds->getExplain()->getExplanationFor(vs[k], ut, mexp, vsit);
              msu[k] = ut;
            }
            if (!mexp.empty())
            {
              Node en =
                  mexp.size() == 1 ? mexp[0] : nm->mkNode(kind::AND, mexp);
              cre_lem = nm->mkNode(kind::OR, en.negate(), neg_guard);
            }
            else
            {
              cre_lem = neg_guard;
            }
          }
          if (!cre_lem.isNull())
          {
            if (std::find(lems.begin(), lems.end(), cre_lem) == lems.end())
            {
              Trace("sygus-cref-eval") << "...produced lemma : " << cre_lem
                                       << std::endl;
              lems.push_back(cre_lem);
            }
          }
        }
      }
    }
  }
}

bool Cegis::sampleAddRefinementLemma(const std::vector<Node>& candidates,
                                     const std::vector<Node>& vals,
                                     std::vector<Node>& lems)
{
  if (Trace.isOn("cegis-sample"))
  {
    Trace("cegis-sample") << "Check sampling for candidate solution"
                          << std::endl;
    for (unsigned i = 0, size = vals.size(); i < size; i++)
    {
      Trace("cegis-sample") << "  " << candidates[i] << " -> " << vals[i]
                            << std::endl;
    }
  }
  Assert(vals.size() == candidates.size());
  Node sbody = d_base_body.substitute(
      candidates.begin(), candidates.end(), vals.begin(), vals.end());
  Trace("cegis-sample-debug") << "Sample " << sbody << std::endl;
  // do eager unfolding
  std::map<Node, Node> visited_n;
  sbody = d_qe->getTermDatabaseSygus()->getEagerUnfold(sbody, visited_n);
  Trace("cegis-sample") << "Sample (after unfolding): " << sbody << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = d_cegis_sampler.getNumSamplePoints(); i < size;
       i++)
  {
    if (d_cegis_sample_refine.find(i) == d_cegis_sample_refine.end())
    {
      Node ev = d_cegis_sampler.evaluate(sbody, i);
      Trace("cegis-sample-debug") << "...evaluate point #" << i << " to " << ev
                                  << std::endl;
      Assert(ev.isConst());
      Assert(ev.getType().isBoolean());
      if (!ev.getConst<bool>())
      {
        Trace("cegis-sample-debug") << "...false for point #" << i << std::endl;
        // mark this as a CEGIS point (no longer sampled)
        d_cegis_sample_refine.insert(i);
        std::vector<Node> vars;
        std::vector<Node> pt;
        d_cegis_sampler.getSamplePoint(i, vars, pt);
        Assert(d_base_vars.size() == pt.size());
        Node rlem = d_base_body.substitute(
            d_base_vars.begin(), d_base_vars.end(), pt.begin(), pt.end());
        rlem = Rewriter::rewrite(rlem);
        if (std::find(
                d_refinement_lemmas.begin(), d_refinement_lemmas.end(), rlem)
            == d_refinement_lemmas.end())
        {
          if (Trace.isOn("cegis-sample"))
          {
            Trace("cegis-sample") << "   false for point #" << i << " : ";
            for (const Node& cn : pt)
            {
              Trace("cegis-sample") << cn << " ";
            }
            Trace("cegis-sample") << std::endl;
          }
          Trace("cegqi-engine") << "  *** Refine by sampling" << std::endl;
          d_refinement_lemmas.push_back(rlem);
          // if trust, we are not interested in sending out refinement lemmas
          if (options::cegisSample() != CEGIS_SAMPLE_TRUST)
          {
            Node lem = nm->mkNode(OR, d_parent->getGuard().negate(), rlem);
            lems.push_back(lem);
          }
          return true;
        }
        else
        {
          Trace("cegis-sample-debug") << "...duplicate." << std::endl;
        }
      }
    }
  }
  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
