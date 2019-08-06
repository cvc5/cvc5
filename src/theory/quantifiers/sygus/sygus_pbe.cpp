/*********************                                                        */
/*! \file sygus_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/sygus_pbe.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
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

//--------------------------------- collecting finite input/output domain information

bool SygusPbe::collectExamples(Node n,
                               std::map<Node, bool>& visited,
                               bool hasPol,
                               bool pol)
{
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    Node neval;
    Node n_output;
    bool neval_is_evalapp = false;
    if (n.getKind() == DT_SYGUS_EVAL)
    {
      neval = n;
      if( hasPol ){
        n_output = pol ? d_true : d_false;
      }
      neval_is_evalapp = true;
    }
    else if (n.getKind() == EQUAL && hasPol && pol)
    {
      for( unsigned r=0; r<2; r++ ){
        if (n[r].getKind() == DT_SYGUS_EVAL)
        {
          neval = n[r];
          if( n[1-r].isConst() ){
            n_output = n[1-r];
          }
          neval_is_evalapp = true;
        }
      }
    }
    // is it an evaluation function?
    if (neval_is_evalapp && d_examples.find(neval[0]) != d_examples.end())
    {
      Trace("sygus-pbe-debug")
          << "Process head: " << n << " == " << n_output << std::endl;
      // If n_output is null, then neval does not have a constant value
      // If n_output is non-null, then neval is constrained to always be
      // that value.
      if (!n_output.isNull())
      {
        std::map<Node, Node>::iterator itet = d_exampleTermMap.find(neval);
        if (itet == d_exampleTermMap.end())
        {
          d_exampleTermMap[neval] = n_output;
        }
        else if (itet->second != n_output)
        {
          // We have a conflicting pair f( c ) = d1 ^ f( c ) = d2 for d1 != d2,
          // the conjecture is infeasible.
          return false;
        }
      }
      // get the evaluation head
      Node eh = neval[0];
      std::map<Node, bool>::iterator itx = d_examples_invalid.find(eh);
      if (itx == d_examples_invalid.end())
      {
        // collect example
        bool success = true;
        std::vector<Node> ex;
        for (unsigned j = 1, nchild = neval.getNumChildren(); j < nchild; j++)
        {
          if (!neval[j].isConst())
          {
            success = false;
            break;
          }
          ex.push_back(neval[j]);
        }
        if (success)
        {
          d_examples[eh].push_back(ex);
          d_examples_out[eh].push_back(n_output);
          d_examples_term[eh].push_back(neval);
          if (n_output.isNull())
          {
            d_examples_out_invalid[eh] = true;
          }
          else
          {
            Assert(n_output.isConst());
          }
          // finished processing this node
          return true;
        }
        d_examples_invalid[eh] = true;
        d_examples_out_invalid[eh] = true;
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getEntailPolarity(n, i, hasPol, pol, newHasPol, newPol);
      if (!collectExamples(n[i], visited, newHasPol, newPol))
      {
        return false;
      }
    }
  }
  return true;
}

bool SygusPbe::initialize(Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas)
{
  Trace("sygus-pbe") << "Initialize PBE : " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  for (unsigned i = 0; i < candidates.size(); i++)
  {
    Node v = candidates[i];
    d_examples[v].clear();
    d_examples_out[v].clear();
    d_examples_term[v].clear();
  }

  std::map<Node, bool> visited;
  // n is negated conjecture
  if (!collectExamples(n, visited, true, false))
  {
    Trace("sygus-pbe") << "...conflicting examples" << std::endl;
    Node infeasible = d_parent->getGuard().negate();
    lemmas.push_back(infeasible);
    return false;
  }

  for (unsigned i = 0; i < candidates.size(); i++)
  {
    Node v = candidates[i];
    Trace("sygus-pbe") << "  examples for " << v << " : ";
    if (d_examples_invalid.find(v) != d_examples_invalid.end())
    {
      Trace("sygus-pbe") << "INVALID" << std::endl;
    }
    else
    {
      Trace("sygus-pbe") << std::endl;
      for (unsigned j = 0; j < d_examples[v].size(); j++)
      {
        Trace("sygus-pbe") << "    ";
        for (unsigned k = 0; k < d_examples[v][j].size(); k++)
        {
          Trace("sygus-pbe") << d_examples[v][j][k] << " ";
        }
        if (!d_examples_out[v][j].isNull())
        {
          Trace("sygus-pbe") << " -> " << d_examples_out[v][j];
        }
        Trace("sygus-pbe") << std::endl;
      }
    }
  }

  if (!options::sygusUnifPbe())
  {
    // we are not doing unification
    return false;
  }

  // check if all candidates are valid examples
  d_is_pbe = true;
  for (const Node& c : candidates)
  {
    if (d_examples[c].empty()
        || d_examples_out_invalid.find(c) != d_examples_out_invalid.end())
    {
      d_is_pbe = false;
      return false;
    }
  }
  for (const Node& c : candidates)
  {
    Assert(d_examples.find(c) != d_examples.end());
    Trace("sygus-pbe") << "Initialize unif utility for " << c << "..."
                       << std::endl;
    std::map<Node, std::vector<Node>> strategy_lemmas;
    d_sygus_unif[c].initializeCandidate(
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
      d_tds->registerEnumerator(e, c, d_parent, ROLE_ENUM_POOL, false);
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
    Trace("sygus-pbe") << "Initialize " << d_examples[c].size()
                       << " example points for " << c << "..." << std::endl;
    // initialize the examples
    for (unsigned i = 0, nex = d_examples[c].size(); i < nex; i++)
    {
      d_sygus_unif[c].addExample(d_examples[c][i], d_examples_out[c][i]);
    }
  }
  return true;
}

Node SygusPbe::PbeTrie::addTerm(Node b, const std::vector<Node>& exOut)
{
  PbeTrie* curr = this;
  for (const Node& eo : exOut)
  {
    curr = &(curr->d_children[eo]);
  }
  if (!curr->d_children.empty())
  {
    return curr->d_children.begin()->first;
  }
  curr->d_children.insert(std::pair<Node, PbeTrie>(b, PbeTrie()));
  return b;
}

bool SygusPbe::hasExamples(Node e)
{
  if (isPbe()) {
    e = d_tds->getSynthFunForEnumerator(e);
    Assert(!e.isNull());
    std::map<Node, bool>::iterator itx = d_examples_invalid.find(e);
    if (itx == d_examples_invalid.end()) {
      return d_examples.find(e) != d_examples.end();
    }
  }
  return false;
}

unsigned SygusPbe::getNumExamples(Node e)
{
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, std::vector<std::vector<Node> > >::iterator it =
      d_examples.find(e);
  if (it != d_examples.end()) {
    return it->second.size();
  } else {
    return 0;
  }
}

void SygusPbe::getExample(Node e, unsigned i, std::vector<Node>& ex)
{
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, std::vector<std::vector<Node> > >::iterator it =
      d_examples.find(e);
  if (it != d_examples.end()) {
    Assert(i < it->second.size());
    ex.insert(ex.end(), it->second[i].begin(), it->second[i].end());
  } else {
    Assert(false);
  }
}

Node SygusPbe::getExampleOut(Node e, unsigned i)
{
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, std::vector<Node> >::iterator it = d_examples_out.find(e);
  if (it != d_examples_out.end()) {
    Assert(i < it->second.size());
    return it->second[i];
  } else {
    Assert(false);
    return Node::null();
  }
}

Node SygusPbe::addSearchVal(TypeNode tn, Node e, Node bvr)
{
  Assert(isPbe());
  Assert(!e.isNull());
  if (d_tds->isVariableAgnosticEnumerator(e))
  {
    // we cannot apply conjecture-specific symmetry breaking on variable
    // agnostic enumerators
    return Node::null();
  }
  Node ee = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, bool>::iterator itx = d_examples_invalid.find(ee);
  if (itx == d_examples_invalid.end()) {
    // compute example values with the I/O utility
    std::vector<Node> vals;
    Trace("sygus-pbe-debug")
        << "Compute examples " << bvr << "..." << std::endl;
    d_sygus_unif[ee].computeExamples(e, bvr, vals);
    Assert(vals.size() == d_examples[ee].size());
    Trace("sygus-pbe-debug") << "...got " << vals << std::endl;
    Trace("sygus-pbe-debug") << "Add to trie..." << std::endl;
    Node ret = d_pbe_trie[e][tn].addTerm(bvr, vals);
    Trace("sygus-pbe-debug") << "...got " << ret << std::endl;
    if (ret != bvr)
    {
      Trace("sygus-pbe-debug") << "...clear example cache" << std::endl;
      d_sygus_unif[ee].clearExampleCache(e, bvr);
    }
    Assert(ret.getType() == bvr.getType());
    return ret;
  }
  return Node::null();
}

Node SygusPbe::evaluateBuiltin(TypeNode tn, Node bn, Node e, unsigned i)
{
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, bool>::iterator itx = d_examples_invalid.find(e);
  if (itx == d_examples_invalid.end()) {
    std::map<Node, std::vector<std::vector<Node> > >::iterator it =
        d_examples.find(e);
    if (it != d_examples.end()) {
      Assert(i < it->second.size());
      return d_tds->evaluateBuiltin(tn, bn, it->second[i]);
    }
  }
  return Rewriter::rewrite(bn);
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
  Assert( enums.size()==enum_values.size() );
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
      d_sygus_unif[c].notifyEnumeration(e, v, enum_lems);
      if (!enum_lems.empty())
      {
        // the lemmas must be guarded by the active guard of the enumerator
        Node g = d_tds->getActiveGuardForEnumerator(e);
        Assert(!g.isNull());
        for (unsigned j = 0, size = enum_lems.size(); j < size; j++)
        {
          enum_lems[j] = nm->mkNode(OR, g.negate(), enum_lems[j]);
        }
        lems.insert(lems.end(), enum_lems.begin(), enum_lems.end());
      }
    }
  }
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node c = candidates[i];
    //build decision tree for candidate
    std::vector<Node> sol;
    if (d_sygus_unif[c].constructSolution(sol, lems))
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
