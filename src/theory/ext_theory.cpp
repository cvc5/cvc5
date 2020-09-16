/*********************                                                        */
/*! \file ext_theory.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extended theory interface.
 **
 ** This implements a generic module, used by theory solvers, for performing
 ** "context-dependent simplification", as described in Reynolds et al
 ** "Designing Theory Solvers with Extensions", FroCoS 2017.
 **/

#include "theory/ext_theory.h"

#include "base/check.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers_engine.h"
#include "theory/substitutions.h"

using namespace std;

namespace CVC4 {
namespace theory {

bool ExtTheoryCallback::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node> >& exp)
{
  return false;
}
bool ExtTheoryCallback::isExtfReduced(int effort,
                                      Node n,
                                      Node on,
                                      std::vector<Node>& exp)
{
  return n.isConst();
}
bool ExtTheoryCallback::getReduction(int effort,
                                    Node n,
                                    Node& nr,
                                    bool& isSatDep)
{
  return false;
}

ExtTheory::ExtTheory(ExtTheoryCallback& p,
                     context::Context* c,
                     context::UserContext* u,
                     OutputChannel& out,
                     bool cacheEnabled)
    : d_parent(p),
      d_out(out),
      d_ext_func_terms(c),
      d_ci_inactive(u),
      d_has_extf(c),
      d_lemmas(u),
      d_pp_lemmas(u),
      d_cacheEnabled(cacheEnabled)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

// Gets all leaf terms in n.
std::vector<Node> ExtTheory::collectVars(Node n)
{
  std::vector<Node> vars;
  std::set<Node> visited;
  std::vector<Node> worklist;
  worklist.push_back(n);
  while (!worklist.empty())
  {
    Node current = worklist.back();
    worklist.pop_back();
    if (current.isConst() || visited.count(current) > 0)
    {
      continue;
    }
    visited.insert(current);
    // Treat terms not belonging to this theory as leaf
    // note : chould include terms not belonging to this theory
    // (commented below)
    if (current.getNumChildren() > 0)
    {
      worklist.insert(worklist.end(), current.begin(), current.end());
    }
    else
    {
      vars.push_back(current);
    }
  }
  return vars;
}

Node ExtTheory::getSubstitutedTerm(int effort,
                                   Node term,
                                   std::vector<Node>& exp,
                                   bool useCache)
{
  if (useCache)
  {
    Assert(d_gst_cache[effort].find(term) != d_gst_cache[effort].end());
    exp.insert(exp.end(),
               d_gst_cache[effort][term].d_exp.begin(),
               d_gst_cache[effort][term].d_exp.end());
    return d_gst_cache[effort][term].d_sterm;
  }

  std::vector<Node> terms;
  terms.push_back(term);
  std::vector<Node> sterms;
  std::vector<std::vector<Node> > exps;
  getSubstitutedTerms(effort, terms, sterms, exps, useCache);
  Assert(sterms.size() == 1);
  Assert(exps.size() == 1);
  exp.insert(exp.end(), exps[0].begin(), exps[0].end());
  return sterms[0];
}

// do inferences
void ExtTheory::getSubstitutedTerms(int effort,
                                    const std::vector<Node>& terms,
                                    std::vector<Node>& sterms,
                                    std::vector<std::vector<Node> >& exp,
                                    bool useCache)
{
  if (useCache)
  {
    for (const Node& n : terms)
    {
      Assert(d_gst_cache[effort].find(n) != d_gst_cache[effort].end());
      sterms.push_back(d_gst_cache[effort][n].d_sterm);
      exp.push_back(std::vector<Node>());
      exp[0].insert(exp[0].end(),
                    d_gst_cache[effort][n].d_exp.begin(),
                    d_gst_cache[effort][n].d_exp.end());
    }
  }
  else
  {
    Trace("extt-debug") << "getSubstitutedTerms for " << terms.size() << " / "
                        << d_ext_func_terms.size() << " extended functions."
                        << std::endl;
    if (!terms.empty())
    {
      // all variables we need to find a substitution for
      std::vector<Node> vars;
      std::vector<Node> sub;
      std::map<Node, std::vector<Node> > expc;
      for (const Node& n : terms)
      {
        // do substitution, rewrite
        std::map<Node, ExtfInfo>::iterator iti = d_extf_info.find(n);
        Assert(iti != d_extf_info.end());
        for (const Node& v : iti->second.d_vars)
        {
          if (std::find(vars.begin(), vars.end(), v) == vars.end())
          {
            vars.push_back(v);
          }
        }
      }
      bool useSubs = d_parent.getCurrentSubstitution(effort, vars, sub, expc);
      // get the current substitution for all variables
      Assert(!useSubs || vars.size() == sub.size());
      for (const Node& n : terms)
      {
        Node ns = n;
        std::vector<Node> expn;
        if (useSubs)
        {
          // do substitution
          ns = n.substitute(vars.begin(), vars.end(), sub.begin(), sub.end());
          if (ns != n)
          {
            // build explanation: explanation vars = sub for each vars in FV(n)
            std::map<Node, ExtfInfo>::iterator iti = d_extf_info.find(n);
            Assert(iti != d_extf_info.end());
            for (const Node& v : iti->second.d_vars)
            {
              std::map<Node, std::vector<Node> >::iterator itx = expc.find(v);
              if (itx != expc.end())
              {
                for (const Node& e : itx->second)
                {
                  if (std::find(expn.begin(), expn.end(), e) == expn.end())
                  {
                    expn.push_back(e);
                  }
                }
              }
            }
          }
          Trace("extt-debug")
              << "  have " << n << " == " << ns << ", exp size=" << expn.size()
              << "." << std::endl;
        }
        // add to vector
        sterms.push_back(ns);
        exp.push_back(expn);
        // add to cache
        if (d_cacheEnabled)
        {
          d_gst_cache[effort][n].d_sterm = ns;
          d_gst_cache[effort][n].d_exp.clear();
          d_gst_cache[effort][n].d_exp.insert(
              d_gst_cache[effort][n].d_exp.end(), expn.begin(), expn.end());
        }
      }
    }
  }
}

bool ExtTheory::doInferencesInternal(int effort,
                                     const std::vector<Node>& terms,
                                     std::vector<Node>& nred,
                                     bool batch,
                                     bool isRed)
{
  if (batch)
  {
    bool addedLemma = false;
    if (isRed)
    {
      for (const Node& n : terms)
      {
        Node nr;
        // note: could do reduction with substitution here
        bool satDep = false;
        if (!d_parent.getReduction(effort, n, nr, satDep))
        {
          nred.push_back(n);
        }
        else
        {
          if (!nr.isNull() && n != nr)
          {
            Node lem = NodeManager::currentNM()->mkNode(kind::EQUAL, n, nr);
            if (sendLemma(lem, true))
            {
              Trace("extt-lemma")
                  << "ExtTheory : reduction lemma : " << lem << std::endl;
              addedLemma = true;
            }
          }
          markReduced(n, satDep);
        }
      }
    }
    else
    {
      std::vector<Node> sterms;
      std::vector<std::vector<Node> > exp;
      getSubstitutedTerms(effort, terms, sterms, exp);
      std::map<Node, unsigned> sterm_index;
      NodeManager* nm = NodeManager::currentNM();
      for (unsigned i = 0, size = terms.size(); i < size; i++)
      {
        bool processed = false;
        if (sterms[i] != terms[i])
        {
          Node sr = Rewriter::rewrite(sterms[i]);
          // ask the theory if this term is reduced, e.g. is it constant or it
          // is a non-extf term.
          if (d_parent.isExtfReduced(effort, sr, terms[i], exp[i]))
          {
            processed = true;
            markReduced(terms[i]);
            // We have exp[i] => terms[i] = sr, convert this to a clause.
            // This ensures the proof infrastructure can process this as a
            // normal theory lemma.
            Node eq = terms[i].eqNode(sr);
            Node lem = eq;
            if (!exp[i].empty())
            {
              std::vector<Node> eei;
              for (const Node& e : exp[i])
              {
                eei.push_back(e.negate());
              }
              eei.push_back(eq);
              lem = nm->mkNode(kind::OR, eei);
            }

            Trace("extt-debug") << "ExtTheory::doInferences : infer : " << eq
                                << " by " << exp[i] << std::endl;
            Trace("extt-debug") << "...send lemma " << lem << std::endl;
            if (sendLemma(lem))
            {
              Trace("extt-lemma")
                  << "ExtTheory : substitution + rewrite lemma : " << lem
                  << std::endl;
              addedLemma = true;
            }
          }
          else
          {
            // check if we have already reduced this
            std::map<Node, unsigned>::iterator itsi = sterm_index.find(sr);
            if (itsi == sterm_index.end())
            {
              sterm_index[sr] = i;
            }
            else
            {
              // unsigned j = itsi->second;
              // note : can add (non-reducing) lemma :
              //   exp[j] ^ exp[i] => sterms[i] = sterms[j]
            }

            Trace("extt-nred") << "Non-reduced term : " << sr << std::endl;
          }
        }
        else
        {
          Trace("extt-nred") << "Non-reduced term : " << sterms[i] << std::endl;
        }
        if (!processed)
        {
          nred.push_back(terms[i]);
        }
      }
    }
    return addedLemma;
  }
  // non-batch
  std::vector<Node> nnred;
  if (terms.empty())
  {
    for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
         it != d_ext_func_terms.end();
         ++it)
    {
      if ((*it).second && !isContextIndependentInactive((*it).first))
      {
        std::vector<Node> nterms;
        nterms.push_back((*it).first);
        if (doInferencesInternal(effort, nterms, nnred, true, isRed))
        {
          return true;
        }
      }
    }
  }
  else
  {
    for (const Node& n : terms)
    {
      std::vector<Node> nterms;
      nterms.push_back(n);
      if (doInferencesInternal(effort, nterms, nnred, true, isRed))
      {
        return true;
      }
    }
  }
  return false;
}

bool ExtTheory::sendLemma(Node lem, bool preprocess)
{
  if (preprocess)
  {
    if (d_pp_lemmas.find(lem) == d_pp_lemmas.end())
    {
      d_pp_lemmas.insert(lem);
      d_out.lemma(lem, LemmaProperty::PREPROCESS);
      return true;
    }
  }
  else
  {
    if (d_lemmas.find(lem) == d_lemmas.end())
    {
      d_lemmas.insert(lem);
      d_out.lemma(lem);
      return true;
    }
  }
  return false;
}

bool ExtTheory::doInferences(int effort,
                             const std::vector<Node>& terms,
                             std::vector<Node>& nred,
                             bool batch)
{
  if (!terms.empty())
  {
    return doInferencesInternal(effort, terms, nred, batch, false);
  }
  return false;
}

bool ExtTheory::doInferences(int effort, std::vector<Node>& nred, bool batch)
{
  std::vector<Node> terms = getActive();
  return doInferencesInternal(effort, terms, nred, batch, false);
}

bool ExtTheory::doReductions(int effort,
                             const std::vector<Node>& terms,
                             std::vector<Node>& nred,
                             bool batch)
{
  if (!terms.empty())
  {
    return doInferencesInternal(effort, terms, nred, batch, true);
  }
  return false;
}

bool ExtTheory::doReductions(int effort, std::vector<Node>& nred, bool batch)
{
  const std::vector<Node> terms = getActive();
  return doInferencesInternal(effort, terms, nred, batch, true);
}

// Register term.
void ExtTheory::registerTerm(Node n)
{
  if (d_extf_kind.find(n.getKind()) != d_extf_kind.end())
  {
    if (d_ext_func_terms.find(n) == d_ext_func_terms.end())
    {
      Trace("extt-debug") << "Found extended function : " << n << std::endl;
      d_ext_func_terms[n] = true;
      d_has_extf = n;
      d_extf_info[n].d_vars = collectVars(n);
    }
  }
}

void ExtTheory::registerTermRec(Node n)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      registerTerm(cur);
      for (const Node& cc : cur)
      {
        visit.push_back(cc);
      }
    }
  } while (!visit.empty());
}

// mark reduced
void ExtTheory::markReduced(Node n, bool satDep)
{
  Trace("extt-debug") << "Mark reduced " << n << std::endl;
  registerTerm(n);
  Assert(d_ext_func_terms.find(n) != d_ext_func_terms.end());
  d_ext_func_terms[n] = false;
  if (!satDep)
  {
    d_ci_inactive.insert(n);
  }

  // update has_extf
  if (d_has_extf.get() == n)
  {
    for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
         it != d_ext_func_terms.end();
         ++it)
    {
      // if not already reduced
      if ((*it).second && !isContextIndependentInactive((*it).first))
      {
        d_has_extf = (*it).first;
      }
    }
  }
}

// mark congruent
void ExtTheory::markCongruent(Node a, Node b)
{
  Trace("extt-debug") << "Mark congruent : " << a << " " << b << std::endl;
  registerTerm(a);
  registerTerm(b);
  NodeBoolMap::const_iterator it = d_ext_func_terms.find(b);
  if (it != d_ext_func_terms.end())
  {
    if (d_ext_func_terms.find(a) != d_ext_func_terms.end())
    {
      d_ext_func_terms[a] = d_ext_func_terms[a] && (*it).second;
    }
    else
    {
      Assert(false);
    }
    d_ext_func_terms[b] = false;
  }
  else
  {
    Assert(false);
  }
}

bool ExtTheory::isContextIndependentInactive(Node n) const
{
  return d_ci_inactive.find(n) != d_ci_inactive.end();
}

void ExtTheory::getTerms(std::vector<Node>& terms)
{
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end();
       ++it)
  {
    terms.push_back((*it).first);
  }
}

bool ExtTheory::hasActiveTerm() const { return !d_has_extf.get().isNull(); }

// is active
bool ExtTheory::isActive(Node n) const
{
  NodeBoolMap::const_iterator it = d_ext_func_terms.find(n);
  if (it != d_ext_func_terms.end())
  {
    return (*it).second && !isContextIndependentInactive(n);
  }
  return false;
}

// get active
std::vector<Node> ExtTheory::getActive() const
{
  std::vector<Node> active;
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end();
       ++it)
  {
    // if not already reduced
    if ((*it).second && !isContextIndependentInactive((*it).first))
    {
      active.push_back((*it).first);
    }
  }
  return active;
}

std::vector<Node> ExtTheory::getActive(Kind k) const
{
  std::vector<Node> active;
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end();
       ++it)
  {
    // if not already reduced
    if ((*it).first.getKind() == k && (*it).second
        && !isContextIndependentInactive((*it).first))
    {
      active.push_back((*it).first);
    }
  }
  return active;
}

void ExtTheory::clearCache() { d_gst_cache.clear(); }

} /* CVC4::theory namespace */
} /* CVC4 namespace */
