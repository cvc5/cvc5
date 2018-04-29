/*********************                                                        */
/*! \file sygus_unif_rl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif_rl
 **/

#include "theory/quantifiers/sygus/sygus_unif_rl.h"

#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusUnifRl::SygusUnifRl() {}

SygusUnifRl::~SygusUnifRl() {}

void SygusUnifRl::initialize(QuantifiersEngine* qe,
                             Node f,
                             std::vector<Node>& enums,
                             std::vector<Node>& lemmas)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_prev_rlemmas = d_true;
  d_rlemmas = d_true;
  d_hasRLemmas = false;
  d_ecache.clear();
  SygusUnif::initialize(qe, f, enums, lemmas);
}

void SygusUnifRl::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
  Trace("sygus-unif-rl-notify") << "SyGuSUnifRl: Adding to enum " << e
                                << " value " << v << "\n";
  d_ecache[e].d_enum_vals.push_back(v);
  /* Exclude v from next enumerations for e */
  Node exc_lemma =
      d_tds->getExplain()->getExplanationForEquality(e, v).negate();
  Trace("sygus-unif-rl-notify")
      << "SygusUnifRl : enumeration exclude lemma : " << exc_lemma << std::endl;
  lemmas.push_back(exc_lemma);
}

void SygusUnifRl::addRefLemma(Node lemma)
{
  d_prev_rlemmas = d_rlemmas;
  d_rlemmas = d_tds->getExtRewriter()->extendedRewrite(
      NodeManager::currentNM()->mkNode(AND, d_rlemmas, lemma));
  Trace("sygus-unif-rl-lemma")
      << "SyGuSUnifRl: New collection of ref lemmas is " << d_rlemmas << "\n";
  d_hasRLemmas = d_rlemmas != d_true;
}

void SygusUnifRl::collectPoints(Node n)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) != visited.end())
    {
      continue;
    }
    visited.insert(cur);
    unsigned size = cur.getNumChildren();
    if (cur.getKind() == APPLY_UF && size > 0)
    {
      std::vector<Node> pt;
      for (unsigned i = 1; i < size; ++i)
      {
        Assert(cur[i].isConst());
        pt.push_back(cur[i]);
      }
      d_app_to_pt[cur] = pt;
      continue;
    }
    for (const TNode& child : cur)
    {
      visit.push_back(child);
    }
  } while (!visit.empty());
}

void SygusUnifRl::initializeConstructSol()
{
  if (d_hasRLemmas && d_rlemmas != d_prev_rlemmas)
  {
    collectPoints(d_rlemmas);
    if (Trace.isOn("sygus-unif-rl-sol"))
    {
      Trace("sygus-unif-rl-sol") << "SyGuSUnifRl: Points from " << d_rlemmas
                                 << "\n";
      for (const std::pair<Node, std::vector<Node>>& pair : d_app_to_pt)
      {
        Trace("sygus-unif-rl-sol") << "...[" << pair.first << "] --> (";
        for (const Node& pt_i : pair.second)
        {
          Trace("sygus-unif-rl-sol") << pt_i << " ";
        }
        Trace("sygus-unif-rl-sol") << ")\n";
      }
    }
  }
}

Node SygusUnifRl::constructSol(Node e, NodeRole nrole, int ind)
{
  Node solution = canCloseBranch(e);
  if (!solution.isNull())
  {
    return solution;
  }
  return Node::null();
}

Node SygusUnifRl::canCloseBranch(Node e)
{
  if (!d_hasRLemmas && !d_ecache[e].d_enum_vals.empty())
  {
    Trace("sygus-unif-rl-sol") << "SyGuSUnifRl: Closed branch and yielded "
                                  << d_ecache[e].d_enum_vals[0] << "\n";
    return d_ecache[e].d_enum_vals[0];
  }
  return Node::null();
}


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
