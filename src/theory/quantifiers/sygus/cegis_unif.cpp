/*********************                                                        */
/*! \file cegis_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for cegis with unification techniques
 **/

#include "theory/quantifiers/sygus/cegis_unif.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegisUnif::CegisUnif(QuantifiersEngine* qe, CegConjecture* p) : Cegis(qe, p)
{
  d_tds = d_qe->getTermDatabaseSygus();
}

CegisUnif::~CegisUnif() {}
bool CegisUnif::initialize(Node n,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& lemmas)
{
  Trace("cegis-unif") << "Initialize CegisUnif : " << n << std::endl;
  /* For regular CEGIS */
  d_base_body = n;
  if (d_base_body.getKind() == NOT && d_base_body[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_body[0][0])
    {
      d_base_vars.push_back(v);
    }
    d_base_body = d_base_body[0][1];
  }
  /* Init UNIF util */
  d_sygus_unif.initialize(d_qe, candidates, d_enums, lemmas);
  /* TODO initialize condition enumerators */
  Trace("cegis-unif") << "Initializing enums for pure Cegis case\n";
  /* Initialize enumerators for case with no unification for any function */
  for (const Node& c : candidates)
  {
    if (!d_unif.usingUnif(c))
    {
      d_tds->registerEnumerator(c, c, d_parent);
    }
  }
  return true;
}

void CegisUnif::getTermList(const std::vector<Node>& candidates,
                            std::vector<Node>& enums)
{
  if (d_no_unif)
  {
    enums.insert(enums.end(), candidates.begin(), candidates.end());
    return;
  }
  Valuation& valuation = d_qe->getValuation();
  for (const Node& e : d_enums)
  {
    Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
    Node g = d_enum_to_active_guard[e];
    /* Get whether the active guard for this enumerator is if so, then there may
       exist more values for it, and hence we add it to enums. */
    Node gstatus = valuation.getSatValue(g);
    if (!gstatus.isNull() && gstatus.getConst<bool>())
    {
      enums.push_back(e);
    }
  }
}

bool CegisUnif::constructCandidates(const std::vector<Node>& enums,
                                    const std::vector<Node>& enum_values,
                                    const std::vector<Node>& candidates,
                                    std::vector<Node>& candidate_values,
                                    std::vector<Node>& lems)
{
  NodeManager* nm = NodeManager::currentNM();
  if (d_no_unif)
  {
    candidate_values.insert(
        candidate_values.end(), enum_values.begin(), enum_values.end());
    if (options::sygusDirectEval())
    {
      bool addedEvalLemmas = false;
      if (options::sygusCRefEval())
      {
        Trace("cegqi-engine")
            << "  *** Do conjecture refinement evaluation...\n";
        /* see if any refinement lemma is refuted by evaluation */
        std::vector<Node> cre_lems;
        getRefinementEvalLemmas(candidates, candidate_values, cre_lems);
        if (!cre_lems.empty())
        {
          for (const Node& lem : cre_lems)
          {
            if (d_qe->addLemma(lem))
            {
              Trace("cegqi-lemma") << "Cegqi::Lemma : cref evaluation : " << lem
                                   << std::endl;
              addedEvalLemmas = true;
            }
          }
          /* we could, but do not return here. experimentally, it is better to
             add
             the lemmas below as well, in parallel. */
        }
      }
      Trace("cegqi-engine") << "  *** Do direct evaluation...\n";
      std::vector<Node> eager_terms, eager_vals, eager_exps;
      for (unsigned i = 0, size = candidates.size(); i < size; ++i)
      {
        Trace("cegqi-debug") << "  register " << candidates[i] << " -> "
                             << candidate_values[i] << std::endl;
        d_tds->registerModelValue(candidates[i],
                                  candidate_values[i],
                                  eager_terms,
                                  eager_vals,
                                  eager_exps);
      }
      Trace("cegqi-debug") << "...produced " << eager_terms.size()
                           << " eager evaluation lemmas.\n";
      for (unsigned i = 0, size = eager_terms.size(); i < size; ++i)
      {
        Node lem = nm->mkNode(
            OR, eager_exps[i].negate(), eager_terms[i].eqNode(eager_vals[i]));
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
  Assert(enums.size() == enum_values.size());
  if (enums.empty())
  {
    return false;
  }
  unsigned min_term_size = 0;
  std::vector<unsigned> enum_consider;
  Trace("cegis-unif-enum") << "Register new enumerated values :\n";
  for (unsigned i = 0, size = enums.size(); i < size; ++i)
  {
    Trace("cegis-unif-enum") << "  " << enums[i] << " -> " << enum_values[i]
                             << std::endl;
    unsigned sz = d_tds->getSygusTermSize(enum_values[i]);
    if (i == 0 || sz < min_term_size)
    {
      enum_consider.clear();
      min_term_size = sz;
      enum_consider.push_back(i);
    }
    else if (sz == min_term_size)
    {
      enum_consider.push_back(i);
    }
  }
  /* only consider the enumerators that are at minimum size (for fairness) */
  Trace("cegis-unif-enum") << "...register " << enum_consider.size() << " / "
                           << enums.size() << std::endl;
  for (unsigned i = 0, ecsize = enum_consider.size(); i < ecsize; ++i)
  {
    unsigned j = enum_consider[i];
    Node e = enums[j], v = enum_values[j];
    std::vector<Node> enum_lems;
    d_sygus_unif.notifyEnumeration(e, v, enum_lems);
    /* the lemmas must be guarded by the active guard of the enumerator */
    Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
    Node g = d_enum_to_active_guard[e];
    for (unsigned j = 0, size = enum_lems.size(); j < size; ++j)
    {
      enum_lems[j] = nm->mkNode(OR, g.negate(), enum_lems[j]);
    }
    lems.insert(lems.end(), enum_lems.begin(), enum_lems.end());
  }
  /* divide-and-conquer solution bulding for candidates using unif util */
  std::vector<Node> sols;
  if (d_sygus_unif.constructSolution(sols))
  {
    candidate_values.insert(candidate_values.end(), sols.begin(), sols.end());
    return true;
  }
  return false;
}

void CegisUnif::registerRefinementLemma(const std::vector<Node>& vars,
                                        Node lem,
                                        std::vector<Node>& lems)
{
  d_refinement_lemmas.push_back(lem);
  /* Make the refinement lemma and add it to lems. This lemma is guarded by the
     parent's guard, which has the semantics "this conjecture has a solution",
     hence this lemma states: if the parent conjecture has a solution, it
     satisfies the specification for the given concrete point. */
  lems.push_back(
      NodeManager::currentNM()->mkNode(OR, d_parent->getGuard().negate(), lem));
  /* Notify lemma to unification utility */
  d_sygus_unif.addRefLemma(lem);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
