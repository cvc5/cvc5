/*********************                                                        */
/*! \file example_infer.cpp
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
#include "theory/quantifiers/sygus/example_infer.h"

#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/sygus/example_cache.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExampleInfer::ExampleInfer(TermDbSygus* tds) : d_tds(tds)
{
  d_isExamples = false;
}

ExampleInfer::~ExampleInfer() {}

bool ExampleInfer::initialize(Node n, const std::vector<Node>& candidates)
{
  Trace("sygus-pbe") << "Initialize example inference : " << n << std::endl;

  for (const Node& v : candidates)
  {
    d_examples[v].clear();
    d_examplesOut[v].clear();
    d_examplesTerm[v].clear();
  }

  std::map<Node, bool> visited;
  // n is negated conjecture
  if (!collectExamples(n, visited, true, false))
  {
    Trace("sygus-pbe") << "...conflicting examples" << std::endl;
    return false;
  }

  if (Trace.isOn("sygus-pbe"))
  {
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
          if (!d_examplesOut[v][j].isNull())
          {
            Trace("sygus-pbe") << " -> " << d_examplesOut[v][j];
          }
          Trace("sygus-pbe") << std::endl;
        }
      }
      Trace("sygus-pbe") << "Initialize " << d_examples[v].size()
                         << " example points for " << v << "..." << std::endl;
    }
  }
  return true;
}

bool ExampleInfer::collectExamples(Node n,
                                   std::map<Node, bool>& visited,
                                   bool hasPol,
                                   bool pol)
{
  if (visited.find(n) != visited.end())
  {
    // already visited
    return true;
  }
  visited[n] = true;
  NodeManager* nm = NodeManager::currentNM();
  Node neval;
  Node n_output;
  bool neval_is_evalapp = false;
  if (n.getKind() == DT_SYGUS_EVAL)
  {
    neval = n;
    if (hasPol)
    {
      n_output = nm->mkConst(pol);
    }
    neval_is_evalapp = true;
  }
  else if (n.getKind() == EQUAL && hasPol && pol)
  {
    for (unsigned r = 0; r < 2; r++)
    {
      if (n[r].getKind() == DT_SYGUS_EVAL)
      {
        neval = n[r];
        if (n[1 - r].isConst())
        {
          n_output = n[1 - r];
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
        d_examplesOut[eh].push_back(n_output);
        d_examplesTerm[eh].push_back(neval);
        if (n_output.isNull())
        {
          d_examplesOut_invalid[eh] = true;
        }
        else
        {
          Assert(n_output.isConst());
        }
        // finished processing this node
        return true;
      }
      d_examples_invalid[eh] = true;
      d_examplesOut_invalid[eh] = true;
    }
  }
  for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
  {
    bool newHasPol;
    bool newPol;
    QuantPhaseReq::getEntailPolarity(n, i, hasPol, pol, newHasPol, newPol);
    if (!collectExamples(n[i], visited, newHasPol, newPol))
    {
      return false;
    }
  }
  return true;
}

bool ExampleInfer::hasExamples(Node f) const
{
  std::map<Node, bool>::const_iterator itx = d_examples_invalid.find(f);
  if (itx == d_examples_invalid.end())
  {
    return d_examples.find(f) != d_examples.end();
  }
  return false;
}

unsigned ExampleInfer::getNumExamples(Node f) const
{
  std::map<Node, std::vector<std::vector<Node>>>::const_iterator it =
      d_examples.find(f);
  if (it != d_examples.end())
  {
    return it->second.size();
  }
  return 0;
}

void ExampleInfer::getExample(Node f, unsigned i, std::vector<Node>& ex) const
{
  Assert(!f.isNull());
  std::map<Node, std::vector<std::vector<Node>>>::const_iterator it =
      d_examples.find(f);
  if (it != d_examples.end())
  {
    Assert(i < it->second.size());
    ex.insert(ex.end(), it->second[i].begin(), it->second[i].end());
  }
  else
  {
    Assert(false);
  }
}

void ExampleInfer::getExampleTerms(Node f, std::vector<Node>& exTerms) const
{
  std::map<Node, std::vector<Node>>::const_iterator itt =
      d_examplesTerm.find(f);
  if (itt == d_examplesTerm.end())
  {
    return;
  }
  exTerms.insert(exTerms.end(), itt->second.begin(), itt->second.end());
}

Node ExampleInfer::getExampleOut(Node f, unsigned i) const
{
  Assert(!f.isNull());
  std::map<Node, std::vector<Node>>::const_iterator it = d_examplesOut.find(f);
  if (it != d_examplesOut.end())
  {
    Assert(i < it->second.size());
    return it->second[i];
  }
  Assert(false);
  return Node::null();
}

bool ExampleInfer::hasExamplesOut(Node f) const
{
  return d_examplesOut_invalid.find(f) == d_examplesOut_invalid.end();
}

bool ExampleInfer::evaluate(
    Node f, Node e, Node bv, std::vector<Node>& exOut, bool doCache)
{
  if (!hasExamples(f))
  {
    return false;
  }
  // is it in the cache?
  std::map<Node, std::vector<Node>>& eoc = d_exOutCache[e];
  std::map<Node, std::vector<Node>>::iterator it = eoc.find(bv);
  if (it != eoc.end())
  {
    exOut.insert(exOut.end(), it->second.begin(), it->second.end());
    return true;
  }
  // get the evaluation
  evaluateInternal(f, e, bv, exOut);
  // store in cache if necessary
  if (doCache)
  {
    std::vector<Node>& eocv = eoc[bv];
    eocv.insert(eocv.end(), exOut.begin(), exOut.end());
  }
  return true;
}

void ExampleInfer::evaluateInternal(
    Node f, Node e, Node bv, std::vector<Node>& exOut)
{
  // use ExampleCache here
  TypeNode xtn = e.getType();
  SygusTypeInfo& ti = d_tds->getTypeInfo(xtn);
  const std::vector<Node>& varlist = ti.getVarList();
  ExampleCache ec;
  ExampleCacheEvalTds ecetds(d_tds,xtn);
  ec.initialize(bv,varlist,&ecetds);
  Assert(d_examples.find(f) != d_examples.end());
  std::vector<std::vector<Node>>& exs = d_examples[f];
  for (size_t j = 0, esize = exs.size(); j < esize; j++)
  {
    Node res = ec.evaluate(exs[j]);
    //Node res = d_tds->evaluateBuiltin(xtn, bv, exs[j]);
    exOut.push_back(res);
  }
}

Node ExampleInfer::evaluateBuiltin(TypeNode tn, Node bn, Node e, unsigned i)
{
  Node f = d_tds->getSynthFunForEnumerator(e);
  Assert(!f.isNull());
  std::map<Node, bool>::iterator itx = d_examples_invalid.find(f);
  if (itx == d_examples_invalid.end())
  {
    std::map<Node, std::vector<std::vector<Node>>>::iterator it =
        d_examples.find(f);
    if (it != d_examples.end())
    {
      Assert(i < it->second.size());
      return d_tds->evaluateBuiltin(tn, bn, it->second[i]);
    }
  }
  return Rewriter::rewrite(bn);
}

void ExampleInfer::clearEvaluationCache(Node e, Node bv)
{
  std::map<Node, std::vector<Node>>& eoc = d_exOutCache[e];
  Assert(eoc.find(bv) != eoc.end());
  eoc.erase(bv);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
