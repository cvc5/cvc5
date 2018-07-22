/*********************                                                        */
/*! \file sygus_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "util/random.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegConjecturePbe::CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p)
    : SygusModule(qe, p)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_is_pbe = false;
}

CegConjecturePbe::~CegConjecturePbe() {

}

//--------------------------------- collecting finite input/output domain information

void CegConjecturePbe::collectExamples( Node n, std::map< Node, bool >& visited, bool hasPol, bool pol ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    Node neval;
    Node n_output;
    bool neval_is_evalapp = false;
    if (datatypes::DatatypesRewriter::isSygusEvalApp(n))
    {
      neval = n;
      if( hasPol ){
        n_output = !pol ? d_true : d_false;
      }
      neval_is_evalapp = true;
    }else if( n.getKind()==EQUAL && hasPol && !pol ){
      for( unsigned r=0; r<2; r++ ){
        if (datatypes::DatatypesRewriter::isSygusEvalApp(n[r]))
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
          return;
        }
        d_examples_invalid[eh] = true;
        d_examples_out_invalid[eh] = true;
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
      collectExamples( n[i], visited, newHasPol, newPol );
    }
  }
}

bool CegConjecturePbe::initialize(Node n,
                                  const std::vector<Node>& candidates,
                                  std::vector<Node>& lemmas)
{
  Trace("sygus-pbe") << "Initialize PBE : " << n << std::endl;

  for (unsigned i = 0; i < candidates.size(); i++)
  {
    Node v = candidates[i];
    d_examples[v].clear();
    d_examples_out[v].clear();
    d_examples_term[v].clear();
  }

  std::map<Node, bool> visited;
  collectExamples(n, visited, true, true);

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
    NodeManager* nm = NodeManager::currentNM();
    for (const Node& e : d_candidate_to_enum[c])
    {
      TypeNode etn = e.getType();
      d_tds->registerEnumerator(e, c, d_parent, true);
      Node g = d_tds->getActiveGuardForEnumerator(e);
      d_enum_to_active_guard[e] = g;
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
            disj.push_back(lem);
          }
        }
        Node lem = disj.size() == 1 ? disj[0] : nm->mkNode(OR, disj);
        Trace("sygus-pbe") << "  static redundant op lemma : " << lem
                           << std::endl;
        lemmas.push_back(lem);
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

Node CegConjecturePbe::PbeTrie::addPbeExample(TypeNode etn, Node e, Node b,
                                              CegConjecturePbe* cpbe,
                                              unsigned index, unsigned ntotal) {
  if (index == ntotal) {
    // lazy child holds the leaf data
    if (d_lazy_child.isNull()) {
      d_lazy_child = b;
    }
    return d_lazy_child;
  } else {
    std::vector<Node> ex;
    if (d_children.empty()) {
      if (d_lazy_child.isNull()) {
        d_lazy_child = b;
        return d_lazy_child;
      } else {
        // evaluate the lazy child
        Assert(cpbe->d_examples.find(e) != cpbe->d_examples.end());
        Assert(index < cpbe->d_examples[e].size());
        ex = cpbe->d_examples[e][index];
        addPbeExampleEval(etn, e, d_lazy_child, ex, cpbe, index, ntotal);
        Assert(!d_children.empty());
        d_lazy_child = Node::null();
      }
    } else {
      Assert(cpbe->d_examples.find(e) != cpbe->d_examples.end());
      Assert(index < cpbe->d_examples[e].size());
      ex = cpbe->d_examples[e][index];
    }
    return addPbeExampleEval(etn, e, b, ex, cpbe, index, ntotal);
  }
}

Node CegConjecturePbe::PbeTrie::addPbeExampleEval(TypeNode etn, Node e, Node b,
                                                  std::vector<Node>& ex,
                                                  CegConjecturePbe* cpbe,
                                                  unsigned index,
                                                  unsigned ntotal) {
  Node eb = cpbe->d_tds->evaluateBuiltin(etn, b, ex);
  return d_children[eb].addPbeExample(etn, e, b, cpbe, index + 1, ntotal);
}

bool CegConjecturePbe::hasExamples(Node e) {
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

unsigned CegConjecturePbe::getNumExamples(Node e) {
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

void CegConjecturePbe::getExample(Node e, unsigned i, std::vector<Node>& ex) {
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

Node CegConjecturePbe::getExampleOut(Node e, unsigned i) {
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

Node CegConjecturePbe::addSearchVal(TypeNode tn, Node e, Node bvr) {
  Assert(isPbe());
  Assert(!e.isNull());
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, bool>::iterator itx = d_examples_invalid.find(e);
  if (itx == d_examples_invalid.end()) {
    unsigned nex = d_examples[e].size();
    Node ret = d_pbe_trie[e][tn].addPbeExample(tn, e, bvr, this, 0, nex);
    Assert(ret.getType() == bvr.getType());
    return ret;
  }
  return Node::null();
}

Node CegConjecturePbe::evaluateBuiltin(TypeNode tn, Node bn, Node e,
                                       unsigned i) {
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

void CegConjecturePbe::getTermList(const std::vector<Node>& candidates,
                                   std::vector<Node>& terms)
{
  Valuation& valuation = d_qe->getValuation();
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    std::map<Node, std::vector<Node> >::iterator it =
        d_candidate_to_enum.find(v);
    if (it != d_candidate_to_enum.end())
    {
      for (unsigned j = 0; j < it->second.size(); j++)
      {
        Node e = it->second[j];
        Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
        Node g = d_enum_to_active_guard[e];
        // Get whether the active guard for this enumerator is true,
        // if so, then there may exist more values for it, and hence we add it
        // to terms.
        Node gstatus = valuation.getSatValue(g);
        if (!gstatus.isNull() && gstatus.getConst<bool>())
        {
          terms.push_back(e);
        }
      }
    }
  }
}

bool CegConjecturePbe::constructCandidates(const std::vector<Node>& enums,
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
      unsigned sz = d_tds->getSygusTermSize( enum_values[i] );
      szs.push_back(sz);
      if( i==0 || sz<min_term_size ){
        min_term_size = sz;
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
      Assert(szs[i] >= min_term_size);
      int diff = szs[i] - min_term_size;
      if (!options::sygusPbeMultiFair() || diff <= diffAllow)
      {
        enum_consider.push_back( i );
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
      // the lemmas must be guarded by the active guard of the enumerator
      Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
      Node g = d_enum_to_active_guard[e];
      for (unsigned j = 0, size = enum_lems.size(); j < size; j++)
      {
        enum_lems[j] = nm->mkNode(OR, g.negate(), enum_lems[j]);
      }
      lems.insert(lems.end(), enum_lems.begin(), enum_lems.end());
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
