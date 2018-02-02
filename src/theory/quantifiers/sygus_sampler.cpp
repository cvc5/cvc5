/*********************                                                        */
/*! \file sygus_sampler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_sampler
 **/

#include "theory/quantifiers/sygus_sampler.h"

#include "util/bitvector.h"
#include "util/random.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node LazyTrie::add(Node n,
                   LazyTrieEvaluator* ev,
                   unsigned index,
                   unsigned ntotal,
                   bool forceKeep)
{
  LazyTrie* lt = this;
  while (lt != NULL)
  {
    if (index == ntotal)
    {
      // lazy child holds the leaf data
      if (lt->d_lazy_child.isNull() || forceKeep)
      {
        lt->d_lazy_child = n;
      }
      return lt->d_lazy_child;
    }
    std::vector<Node> ex;
    if (lt->d_children.empty())
    {
      if (lt->d_lazy_child.isNull())
      {
        // no one has been here, we are done
        lt->d_lazy_child = n;
        return lt->d_lazy_child;
      }
      // evaluate the lazy child
      Node e_lc = ev->evaluate(lt->d_lazy_child, index);
      // store at next level
      lt->d_children[e_lc].d_lazy_child = lt->d_lazy_child;
      // replace
      lt->d_lazy_child = Node::null();
    }
    // recurse
    Node e = ev->evaluate(n, index);
    lt = &lt->d_children[e];
    index = index + 1;
  }
  return Node::null();
}

SygusSampler::SygusSampler() : d_tds(nullptr), d_is_valid(false) {}

void SygusSampler::initialize(TermDbSygus* tds, Node f, unsigned nsamples)
{
  d_tds = tds;
  d_is_valid = true;
  d_ftn = f.getType();
  Assert(d_ftn.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(d_ftn.toType()).getDatatype();
  Assert(dt.isSygus());

  Trace("sygus-sample") << "Register sampler for " << f << std::endl;

  d_var_index.clear();
  d_type_vars.clear();
  std::vector<TypeNode> types;
  // get the sygus variable list
  Node var_list = Node::fromExpr(dt.getSygusVarList());
  if (!var_list.isNull())
  {
    for (const Node& sv : var_list)
    {
      TypeNode svt = sv.getType();
      d_var_index[sv] = d_type_vars[svt].size();
      d_type_vars[svt].push_back(sv);
      types.push_back(svt);
      Trace("sygus-sample") << "  var #" << types.size() << " : " << sv << " : "
                            << svt << std::endl;
    }
  }

  d_samples.clear();
  for (unsigned i = 0; i < nsamples; i++)
  {
    std::vector<Node> sample_pt;
    Trace("sygus-sample") << "Sample point #" << i << " : ";
    for (unsigned j = 0, size = types.size(); j < size; j++)
    {
      Node r = getRandomValue(types[j]);
      if (r.isNull())
      {
        Trace("sygus-sample") << "INVALID";
        d_is_valid = false;
      }
      Trace("sygus-sample") << r << " ";
      sample_pt.push_back(r);
    }
    Trace("sygus-sample") << std::endl;
    d_samples.push_back(sample_pt);
  }

  d_trie.clear();
}

Node SygusSampler::registerTerm(Node n, bool forceKeep)
{
  if (d_is_valid)
  {
    return d_trie.add(n, this, 0, d_samples.size(), forceKeep);
  }
  return n;
}

bool SygusSampler::isContiguous(Node n)
{
  // compute free variables in n
  std::vector<Node> fvs;
  computeFreeVariables(n, fvs);
  // compute contiguous condition
  for (const std::pair<const TypeNode, std::vector<Node> >& p : d_type_vars)
  {
    bool foundNotFv = false;
    for (const Node& v : p.second)
    {
      bool hasFv = std::find(fvs.begin(), fvs.end(), v) != fvs.end();
      if (!hasFv)
      {
        foundNotFv = true;
      }
      else if (foundNotFv)
      {
        return false;
      }
    }
  }
  return true;
}

void SygusSampler::computeFreeVariables(Node n, std::vector<Node>& fvs)
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
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar())
      {
        if (d_var_index.find(cur) != d_var_index.end())
        {
          fvs.push_back(cur);
        }
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
}

bool SygusSampler::isOrdered(Node n)
{
  // compute free variables in n for each type
  std::map<TypeNode, std::vector<Node> > fvs;

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
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
      if (cur.isVar())
      {
        std::map<Node, unsigned>::iterator itv = d_var_index.find(cur);
        if (itv != d_var_index.end())
        {
          TypeNode tn = cur.getType();
          // if this variable is out of order
          if (itv->second != fvs[tn].size())
          {
            return false;
          }
          fvs[tn].push_back(cur);
        }
      }
      for (unsigned j = 0, nchildren = cur.getNumChildren(); j < nchildren; j++)
      {
        visit.push_back(cur[(nchildren - j) - 1]);
      }
    }
  } while (!visit.empty());
  return true;
}

bool SygusSampler::containsFreeVariables(Node a, Node b)
{
  // compute free variables in a
  std::vector<Node> fvs;
  computeFreeVariables(a, fvs);

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(b);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar())
      {
        if (std::find(fvs.begin(), fvs.end(), cur) == fvs.end())
        {
          return false;
        }
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return true;
}

Node SygusSampler::evaluate(Node n, unsigned index)
{
  Assert(index < d_samples.size());
  Node ev = d_tds->evaluateBuiltin(d_ftn, n, d_samples[index]);
  Trace("sygus-sample-ev") << "( " << n << ", " << index << " ) -> " << ev
                           << std::endl;
  return ev;
}

Node SygusSampler::getRandomValue(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  if (tn.isBoolean())
  {
    return nm->mkConst(Random::getRandom().pickWithProb(0.5));
  }
  else if (tn.isBitVector())
  {
    unsigned sz = tn.getBitVectorSize();
    std::stringstream ss;
    for (unsigned i = 0; i < sz; i++)
    {
      ss << (Random::getRandom().pickWithProb(0.5) ? "1" : "0");
    }
    return nm->mkConst(BitVector(ss.str(), 2));
  }
  else if (tn.isString() || tn.isInteger())
  {
    std::vector<unsigned> vec;
    double ext_freq = .5;
    unsigned base = 10;
    while (Random::getRandom().pickWithProb(ext_freq))
    {
      // add a digit
      vec.push_back(Random::getRandom().pick(0, base));
    }
    if (tn.isString())
    {
      return nm->mkConst(String(vec));
    }
    else if (tn.isInteger())
    {
      Rational baser(base);
      Rational curr(1);
      std::vector<Node> sum;
      for (unsigned j = 0, size = vec.size(); j < size; j++)
      {
        Node digit = nm->mkConst(Rational(vec[j]) * curr);
        sum.push_back(digit);
        curr = curr * baser;
      }
      Node ret;
      if (sum.empty())
      {
        ret = nm->mkConst(Rational(0));
      }
      else if (sum.size() == 1)
      {
        ret = sum[0];
      }
      else
      {
        ret = nm->mkNode(kind::PLUS, sum);
      }

      if (Random::getRandom().pickWithProb(0.5))
      {
        // negative
        ret = nm->mkNode(kind::UMINUS, ret);
      }
      ret = Rewriter::rewrite(ret);
      Assert(ret.isConst());
      return ret;
    }
  }
  else if (tn.isReal())
  {
    Node s = getRandomValue(nm->integerType());
    Node r = getRandomValue(nm->integerType());
    if (!s.isNull() && !r.isNull())
    {
      Rational sr = s.getConst<Rational>();
      Rational rr = s.getConst<Rational>();
      if (rr.sgn() == 0)
      {
        return s;
      }
      else
      {
        return nm->mkConst(sr / rr);
      }
    }
  }
  return Node::null();
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
