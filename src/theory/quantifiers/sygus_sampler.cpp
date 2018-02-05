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

#include "options/quantifiers_options.h"
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

void SygusSampler::initialize(TypeNode tn,
                              std::vector<Node>& vars,
                              unsigned nsamples)
{
  d_tds = nullptr;
  d_is_valid = true;
  d_tn = tn;
  d_ftn = TypeNode::null();
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());
  for (const Node& sv : vars)
  {
    TypeNode svt = sv.getType();
    d_var_index[sv] = d_type_vars[svt].size();
    d_type_vars[svt].push_back(sv);
  }
  d_rvalue_cindices.clear();
  d_rvalue_null_cindices.clear();
  d_var_sygus_types.clear();
  initializeSamples(nsamples);
}

void SygusSampler::initializeSygus(TermDbSygus* tds, Node f, unsigned nsamples)
{
  d_tds = tds;
  d_is_valid = true;
  d_ftn = f.getType();
  Assert(d_ftn.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(d_ftn.toType()).getDatatype();
  Assert(dt.isSygus());
  d_tn = TypeNode::fromType(dt.getSygusType());

  Trace("sygus-sample") << "Register sampler for " << f << std::endl;

  d_var_index.clear();
  d_type_vars.clear();
  // get the sygus variable list
  Node var_list = Node::fromExpr(dt.getSygusVarList());
  if (!var_list.isNull())
  {
    for (const Node& sv : var_list)
    {
      TypeNode svt = sv.getType();
      d_var_index[sv] = d_type_vars[svt].size();
      d_vars.push_back(sv);
      d_type_vars[svt].push_back(sv);
    }
  }
  d_rvalue_cindices.clear();
  d_rvalue_null_cindices.clear();
  d_var_sygus_types.clear();
  registerSygusType(d_ftn);
  initializeSamples(nsamples);
}

void SygusSampler::initializeSamples(unsigned nsamples)
{
  d_samples.clear();
  std::vector<TypeNode> types;
  for (const Node& v : d_vars)
  {
    TypeNode vt = v.getType();
    types.push_back(vt);
    Trace("sygus-sample") << "  var #" << types.size() << " : " << v << " : "
                          << vt << std::endl;
  }
  std::map<unsigned, std::map<Node, std::vector<TypeNode> >::iterator> sts;
  if (options::sygusSampleGrammar())
  {
    for (unsigned j = 0, size = types.size(); j < size; j++)
    {
      sts[j] = d_var_sygus_types.find(d_vars[j]);
    }
  }

  unsigned nduplicates = 0;
  for (unsigned i = 0; i < nsamples; i++)
  {
    std::vector<Node> sample_pt;
    for (unsigned j = 0, size = types.size(); j < size; j++)
    {
      Node v = d_vars[j];
      Node r;
      if (options::sygusSampleGrammar())
      {
        // choose a random start sygus type, if possible
        if (sts[j] != d_var_sygus_types.end())
        {
          unsigned ntypes = sts[j]->second.size();
          Assert(ntypes > 0);
          unsigned index = Random::getRandom().pick(0, ntypes - 1);
          if (index < ntypes)
          {
            // currently hard coded to 0.0, 0.5
            r = getSygusRandomValue(sts[j]->second[index], 0.0, 0.5);
          }
        }
      }
      if (r.isNull())
      {
        r = getRandomValue(types[j]);
        if (r.isNull())
        {
          d_is_valid = false;
        }
      }
      sample_pt.push_back(r);
    }
    if (d_samples_trie.add(sample_pt))
    {
      if (Trace.isOn("sygus-sample"))
      {
        Trace("sygus-sample") << "Sample point #" << i << " : ";
        for (const Node& r : sample_pt)
        {
          Trace("sygus-sample") << r << " ";
        }
        Trace("sygus-sample") << std::endl;
      }
      d_samples.push_back(sample_pt);
    }
    else
    {
      i--;
      nduplicates++;
      if (nduplicates == nsamples * 10)
      {
        Trace("sygus-sample")
            << "...WARNING: excessive duplicates, cut off sampling at " << i
            << "/" << nsamples << " points." << std::endl;
        break;
      }
    }
  }

  d_trie.clear();
}

bool SygusSampler::PtTrie::add(std::vector<Node>& pt)
{
  PtTrie* curr = this;
  for (unsigned i = 0, size = pt.size(); i < size; i++)
  {
    curr = &(curr->d_children[pt[i]]);
  }
  bool retVal = curr->d_children.empty();
  curr = &(curr->d_children[Node::null()]);
  return retVal;
}

Node SygusSampler::registerTerm(Node n, bool forceKeep)
{
  if (d_is_valid)
  {
    Assert(n.getType() == d_tn);
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

void SygusSampler::getSamplePoint(unsigned index, std::vector<Node>& pt)
{
  Assert(index < d_samples.size());
  std::vector<Node>& spt = d_samples[index];
  pt.insert(pt.end(), spt.begin(), spt.end());
}

Node SygusSampler::evaluate(Node n, unsigned index)
{
  Assert(index < d_samples.size());
  // just a substitution
  std::vector<Node>& pt = d_samples[index];
  Node ev = n.substitute(d_vars.begin(), d_vars.end(), pt.begin(), pt.end());
  ev = Rewriter::rewrite(ev);
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

Node SygusSampler::getSygusRandomValue(TypeNode tn,
                                       double rchance,
                                       double rinc,
                                       unsigned depth)
{
  Assert(tn.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  Assert(dt.isSygus());
  Assert(d_rvalue_cindices.find(tn) != d_rvalue_cindices.end());
  Trace("sygus-sample-grammar") << "Sygus random value " << tn
                                << ", depth = " << depth
                                << ", rchance = " << rchance << std::endl;
  // check if we terminate on this call
  // we refuse to enumerate terms of 10+ depth as a hard limit
  bool terminate = Random::getRandom().pickWithProb(rchance) || depth >= 10;
  // if we terminate, only nullary constructors can be chosen
  std::vector<unsigned>& cindices =
      terminate ? d_rvalue_null_cindices[tn] : d_rvalue_cindices[tn];
  unsigned ncons = cindices.size();
  // select a random constructor, or random value when index=ncons.
  unsigned index = Random::getRandom().pick(0, ncons);
  Trace("sygus-sample-grammar") << "Random index 0..." << ncons
                                << " was : " << index << std::endl;
  if (index < ncons)
  {
    Trace("sygus-sample-grammar") << "Recurse constructor index #" << index
                                  << std::endl;
    unsigned cindex = cindices[index];
    Assert(cindex < dt.getNumConstructors());
    const DatatypeConstructor& dtc = dt[cindex];
    // more likely to terminate in recursive calls
    double rchance_new = rchance + (1.0 - rchance) * rinc;
    std::map<int, Node> pre;
    bool success = true;
    // generate random values for all arguments
    for (unsigned i = 0, nargs = dtc.getNumArgs(); i < nargs; i++)
    {
      TypeNode tnc = d_tds->getArgType(dtc, i);
      Node c = getSygusRandomValue(tnc, rchance_new, rinc, depth + 1);
      if (c.isNull())
      {
        success = false;
        Trace("sygus-sample-grammar") << "...fail." << std::endl;
        break;
      }
      Trace("sygus-sample-grammar") << "  child #" << i << " : " << c
                                    << std::endl;
      pre[i] = c;
    }
    if (success)
    {
      Trace("sygus-sample-grammar") << "mkGeneric" << std::endl;
      Node ret = d_tds->mkGeneric(dt, cindex, pre);
      Trace("sygus-sample-grammar") << "...returned " << ret << std::endl;
      ret = Rewriter::rewrite(ret);
      Trace("sygus-sample-grammar") << "...after rewrite " << ret << std::endl;
      Assert(ret.isConst());
      return ret;
    }
  }
  Trace("sygus-sample-grammar") << "...resort to random value" << std::endl;
  // if we did not generate based on the grammar, pick a random value
  return getRandomValue(TypeNode::fromType(dt.getSygusType()));
}

// recursion depth bounded by number of types in grammar (small)
void SygusSampler::registerSygusType(TypeNode tn)
{
  if (d_rvalue_cindices.find(tn) == d_rvalue_cindices.end())
  {
    d_rvalue_cindices[tn].clear();
    Assert(tn.isDatatype());
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    Assert(dt.isSygus());
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DatatypeConstructor& dtc = dt[i];
      Node sop = Node::fromExpr(dtc.getSygusOp());
      bool isVar = std::find(d_vars.begin(), d_vars.end(), sop) != d_vars.end();
      if (isVar)
      {
        // if it is a variable, add it to the list of sygus types for that var
        d_var_sygus_types[sop].push_back(tn);
      }
      else
      {
        // otherwise, it is a constructor for sygus random value
        d_rvalue_cindices[tn].push_back(i);
        if (dtc.getNumArgs() == 0)
        {
          d_rvalue_null_cindices[tn].push_back(i);
        }
      }
      // recurse on all subfields
      for (unsigned j = 0, nargs = dtc.getNumArgs(); j < nargs; j++)
      {
        TypeNode tnc = d_tds->getArgType(dtc, j);
        registerSygusType(tnc);
      }
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
