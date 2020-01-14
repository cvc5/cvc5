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
    d_examples_out[v].clear();
    d_examples_term[v].clear();
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
          if (!d_examples_out[v][j].isNull())
          {
            Trace("sygus-pbe") << " -> " << d_examples_out[v][j];
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

bool ExampleInfer::hasExamples(Node e) const
{
  std::map<Node, bool>::const_iterator itx = d_examples_invalid.find(e);
  if (itx == d_examples_invalid.end())
  {
    return d_examples.find(e) != d_examples.end();
  }
  return false;
}

unsigned ExampleInfer::getNumExamples(Node e) const
{
  std::map<Node, std::vector<std::vector<Node>>>::const_iterator it =
      d_examples.find(e);
  if (it != d_examples.end())
  {
    return it->second.size();
  }
  return 0;
}

void ExampleInfer::getExample(Node e, unsigned i, std::vector<Node>& ex) const
{
  Assert(!e.isNull());
  std::map<Node, std::vector<std::vector<Node>>>::const_iterator it =
      d_examples.find(e);
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

Node ExampleInfer::getExampleOut(Node e, unsigned i) const
{
  Assert(!e.isNull());
  std::map<Node, std::vector<Node>>::const_iterator it = d_examples_out.find(e);
  if (it != d_examples_out.end())
  {
    Assert(i < it->second.size());
    return it->second[i];
  }
  Assert(false);
  return Node::null();
}

bool ExampleInfer::hasExamplesOut(Node e) const
{
  return d_examples_out_invalid.find(e) != d_examples_out_invalid.end();
}

void ExampleInfer::evaluate(Node e,
                            Node bv,
                            std::vector<Node>& exOut,
                            bool doCache)
{
  if (!doCache)
  {
    // TODO: use ExampleCache here
    TypeNode xtn = e.getType();
    std::vector<std::vector<Node>>& exs = d_examples[e];
    for (size_t j = 0, size = d_examples.size(); j < size; j++)
    {
      Node res = d_tds->evaluateBuiltin(xtn, bv, exs[j]);
      exOut.push_back(res);
    }
    return;
  }
  // is it in the cache?
  std::map<Node, std::vector<Node>>& eoc = d_exOutCache[e];
  std::map<Node, std::vector<Node>>::iterator it = eoc.find(bv);
  if (it != eoc.end())
  {
    exOut.insert(exOut.end(), it->second.begin(), it->second.end());
    return;
  }
  // get the evaluation
  evaluate(e, bv, exOut, false);
  // store in cache
  std::vector<Node>& eocv = eoc[bv];
  eocv.insert(eocv.end(), exOut.begin(), exOut.end());
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
