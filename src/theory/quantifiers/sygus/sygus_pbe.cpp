/*********************                                                        */
/*! \file sygus_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/sygus_pbe.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/example_infer.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "util/random.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusPbe::SygusPbe(QuantifiersEngine* qe, SynthConjecture* p)
    : SygusModule(qe, p)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_is_pbe = false;
}

SygusPbe::~SygusPbe() {}

bool SygusPbe::initialize(Node conj,
                          Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas)
{
  Trace("sygus-pbe") << "Initialize PBE : " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  if (!options::sygusUnifPbe())
  {
    // we are not doing unification
    return false;
  }

  // check if all candidates are valid examples
  ExampleInfer* ei = d_parent->getExampleInfer();
  d_is_pbe = true;
  for (const Node& c : candidates)
  {
    // if it has no examples or the output of the examples is invalid
    if (ei->getNumExamples(c) == 0 || !ei->hasExamplesOut(c))
    {
      d_is_pbe = false;
      return false;
    }
  }
  for (const Node& c : candidates)
  {
    Assert(ei->hasExamples(c));
    d_sygus_unif[c].reset(new SygusUnifIo(d_parent));
    Trace("sygus-pbe") << "Initialize unif utility for " << c << "..."
                       << std::endl;
    std::map<Node, std::vector<Node>> strategy_lemmas;
    d_sygus_unif[c]->initializeCandidate(
        d_qe, c, d_candidate_to_enum[c], strategy_lemmas);
    Assert(!d_candidate_to_enum[c].empty());
    Trace("sygus-pbe") << "Initialize " << d_candidate_to_enum[c].size()
                       << " enumerators for " << c << "..." << std::endl;
    // collect list per type of strategy points with strategy lemmas
    std::map<TypeNode, std::vector<Node>> tn_to_strategy_pt;
    for (const std::pair<const Node, std::vector<Node>>& p : strategy_lemmas)
    {
      TypeNode tnsp = p.first.getType();
      tn_to_strategy_pt[tnsp].push_back(p.first);
    }
    // initialize the enumerators
    for (const Node& e : d_candidate_to_enum[c])
    {
      TypeNode etn = e.getType();
      d_tds->registerEnumerator(e, c, d_parent, ROLE_ENUM_POOL);
      d_enum_to_candidate[e] = c;
      TNode te = e;
      // initialize static symmetry breaking lemmas for it
      // we register only one "master" enumerator per type
      // thus, the strategy lemmas (which are for individual strategy points)
      // are applicable (disjunctively) to the master enumerator
      std::map<TypeNode, std::vector<Node>>::iterator itt =
          tn_to_strategy_pt.find(etn);
      if (itt != tn_to_strategy_pt.end())
      {
        std::vector<Node> disj;
        for (const Node& sp : itt->second)
        {
          std::map<Node, std::vector<Node>>::iterator itsl =
              strategy_lemmas.find(sp);
          Assert(itsl != strategy_lemmas.end());
          if (!itsl->second.empty())
          {
            TNode tsp = sp;
            Node lem = itsl->second.size() == 1 ? itsl->second[0]
                                                : nm->mkNode(AND, itsl->second);
            if (tsp != te)
            {
              lem = lem.substitute(tsp, te);
            }
            if (std::find(disj.begin(), disj.end(), lem) == disj.end())
            {
              disj.push_back(lem);
            }
          }
        }
        // add its active guard
        Node ag = d_tds->getActiveGuardForEnumerator(e);
        Assert(!ag.isNull());
        disj.push_back(ag.negate());
        Node lem = disj.size() == 1 ? disj[0] : nm->mkNode(OR, disj);
        // Apply extended rewriting on the lemma. This helps utilities like
        // SygusEnumerator more easily recognize the shape of this lemma, e.g.
        // ( ~is-ite(x) or ( ~is-ite(x) ^ P ) ) --> ~is-ite(x).
        lem = d_tds->getExtRewriter()->extendedRewrite(lem);
        Trace("sygus-pbe") << "  static redundant op lemma : " << lem
                           << std::endl;
        // Register as a symmetry breaking lemma with the term database.
        // This will either be processed via a lemma on the output channel
        // of the sygus extension of the datatypes solver, or internally
        // encoded as a constraint to an active enumerator.
        d_tds->registerSymBreakLemma(e, lem, etn, 0, false);
      }
    }
  }
  return true;
}

// ------------------------------------------- solution construction from enumeration

void SygusPbe::getTermList(const std::vector<Node>& candidates,
                           std::vector<Node>& terms)
{
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    std::map<Node, std::vector<Node> >::iterator it =
        d_candidate_to_enum.find(v);
    if (it != d_candidate_to_enum.end())
    {
      terms.insert(terms.end(), it->second.begin(), it->second.end());
    }
  }
}

bool SygusPbe::allowPartialModel() { return !options::sygusPbeMultiFair(); }

bool SygusPbe::constructCandidates(const std::vector<Node>& enums,
                                   const std::vector<Node>& enum_values,
                                   const std::vector<Node>& candidates,
                                   std::vector<Node>& candidate_values,
                                   std::vector<Node>& lems)
{
  Assert(enums.size() == enum_values.size());
  if( !enums.empty() ){
    unsigned min_term_size = 0;
    Trace("sygus-pbe-enum") << "Register new enumerated values : " << std::endl;
    std::vector<unsigned> szs;
    for (unsigned i = 0, esize = enums.size(); i < esize; i++)
    {
      Trace("sygus-pbe-enum") << "  " << enums[i] << " -> ";
      TermDbSygus::toStreamSygus("sygus-pbe-enum", enum_values[i]);
      Trace("sygus-pbe-enum") << std::endl;
      if (!enum_values[i].isNull())
      {
        unsigned sz = d_tds->getSygusTermSize(enum_values[i]);
        szs.push_back(sz);
        if (i == 0 || sz < min_term_size)
        {
          min_term_size = sz;
        }
      }
      else
      {
        szs.push_back(0);
      }
    }
    // Assume two enumerators of types T1 and T2.
    // If options::sygusPbeMultiFair() is true,
    // we ensure that all values of type T1 and size n are enumerated before
    // any term of type T2 of size n+d, and vice versa, where d is
    // set by options::sygusPbeMultiFairDiff(). If d is zero, then our
    // enumeration is such that all terms of T1 or T2 of size n are considered
    // before any term of size n+1.
    int diffAllow = options::sygusPbeMultiFairDiff();
    std::vector<unsigned> enum_consider;
    for (unsigned i = 0, esize = enums.size(); i < esize; i++)
    {
      if (!enum_values[i].isNull())
      {
        Assert(szs[i] >= min_term_size);
        int diff = szs[i] - min_term_size;
        if (!options::sygusPbeMultiFair() || diff <= diffAllow)
        {
          enum_consider.push_back(i);
        }
      }
    }

    // only consider the enumerators that are at minimum size (for fairness)
    Trace("sygus-pbe-enum") << "...register " << enum_consider.size() << " / " << enums.size() << std::endl;
    NodeManager* nm = NodeManager::currentNM();
    for (unsigned i = 0, ecsize = enum_consider.size(); i < ecsize; i++)
    {
      unsigned j = enum_consider[i];
      Node e = enums[j];
      Node v = enum_values[j];
      Assert(d_enum_to_candidate.find(e) != d_enum_to_candidate.end());
      Node c = d_enum_to_candidate[e];
      std::vector<Node> enum_lems;
      d_sygus_unif[c]->notifyEnumeration(e, v, enum_lems);
      if (!enum_lems.empty())
      {
        // the lemmas must be guarded by the active guard of the enumerator
        Node g = d_tds->getActiveGuardForEnumerator(e);
        Assert(!g.isNull());
        for (unsigned k = 0, size = enum_lems.size(); k < size; k++)
        {
          enum_lems[k] = nm->mkNode(OR, g.negate(), enum_lems[k]);
        }
        lems.insert(lems.end(), enum_lems.begin(), enum_lems.end());
      }
    }
  }
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node c = candidates[i];
    //build decision tree for candidate
    std::vector<Node> sol;
    if (d_sygus_unif[c]->constructSolution(sol, lems))
    {
      Assert(sol.size() == 1);
      candidate_values.push_back(sol[0]);
    }
    else
    {
      return false;
    }
  }
  return true;
}

}
}
}
