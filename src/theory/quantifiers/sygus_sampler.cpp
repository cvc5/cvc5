/*********************                                                        */
/*! \file sygus_sampler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_sampler
 **/

#include "theory/quantifiers/sygus_sampler.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/lazy_trie.h"
#include "util/bitvector.h"
#include "util/random.h"
#include "util/sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusSampler::SygusSampler()
    : d_tds(nullptr), d_use_sygus_type(false), d_is_valid(false)
{
}

void SygusSampler::initialize(TypeNode tn,
                              const std::vector<Node>& vars,
                              unsigned nsamples,
                              bool unique_type_ids)
{
  d_tds = nullptr;
  d_use_sygus_type = false;
  d_is_valid = true;
  d_ftn = TypeNode::null();
  d_type_vars.clear();
  d_vars.clear();
  d_rvalue_cindices.clear();
  d_rvalue_null_cindices.clear();
  d_rstring_alphabet.clear();
  d_var_sygus_types.clear();
  d_const_sygus_types.clear();
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());
  std::map<TypeNode, unsigned> type_to_type_id;
  unsigned type_id_counter = 0;
  for (const Node& sv : d_vars)
  {
    TypeNode svt = sv.getType();
    unsigned tnid = 0;
    if (unique_type_ids)
    {
      tnid = type_id_counter;
      type_id_counter++;
    }
    else
    {
      std::map<TypeNode, unsigned>::iterator itt = type_to_type_id.find(svt);
      if (itt == type_to_type_id.end())
      {
        type_to_type_id[svt] = type_id_counter;
        type_id_counter++;
      }
      else
      {
        tnid = itt->second;
      }
    }
    Trace("sygus-sample-debug")
        << "Type id for " << sv << " is " << tnid << std::endl;
    d_var_index[sv] = d_type_vars[tnid].size();
    d_type_vars[tnid].push_back(sv);
    d_type_ids[sv] = tnid;
  }
  initializeSamples(nsamples);
}

void SygusSampler::initializeSygus(TermDbSygus* tds,
                                   Node f,
                                   unsigned nsamples,
                                   bool useSygusType)
{
  d_tds = tds;
  d_use_sygus_type = useSygusType;
  d_is_valid = true;
  d_ftn = f.getType();
  Assert(d_ftn.isDatatype());
  const DType& dt = d_ftn.getDType();
  Assert(dt.isSygus());

  Trace("sygus-sample") << "Register sampler for " << f << std::endl;

  d_vars.clear();
  d_type_vars.clear();
  d_var_index.clear();
  d_type_vars.clear();
  d_rvalue_cindices.clear();
  d_rvalue_null_cindices.clear();
  d_var_sygus_types.clear();
  // get the sygus variable list
  Node var_list = dt.getSygusVarList();
  if (!var_list.isNull())
  {
    for (const Node& sv : var_list)
    {
      d_vars.push_back(sv);
    }
  }
  // register sygus type
  registerSygusType(d_ftn);
  // Variables are associated with type ids based on the set of sygus types they
  // appear in.
  std::map<Node, unsigned> var_to_type_id;
  unsigned type_id_counter = 0;
  for (const Node& sv : d_vars)
  {
    TypeNode svt = sv.getType();
    // is it equivalent to a previous variable?
    for (const std::pair<Node, unsigned>& v : var_to_type_id)
    {
      Node svc = v.first;
      if (svc.getType() == svt)
      {
        if (d_var_sygus_types[sv].size() == d_var_sygus_types[svc].size())
        {
          bool success = true;
          for (unsigned t = 0, size = d_var_sygus_types[sv].size(); t < size;
               t++)
          {
            if (d_var_sygus_types[sv][t] != d_var_sygus_types[svc][t])
            {
              success = false;
              break;
            }
          }
          if (success)
          {
            var_to_type_id[sv] = var_to_type_id[svc];
          }
        }
      }
    }
    if (var_to_type_id.find(sv) == var_to_type_id.end())
    {
      var_to_type_id[sv] = type_id_counter;
      type_id_counter++;
    }
    unsigned tnid = var_to_type_id[sv];
    Trace("sygus-sample-debug")
        << "Type id for " << sv << " is " << tnid << std::endl;
    d_var_index[sv] = d_type_vars[tnid].size();
    d_type_vars[tnid].push_back(sv);
    d_type_ids[sv] = tnid;
  }

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
          if(ntypes > 0)
          {
            unsigned index = Random::getRandom().pick(0, ntypes - 1);
            if (index < ntypes)
            {
              // currently hard coded to 0.0, 0.5
              r = getSygusRandomValue(sts[j]->second[index], 0.0, 0.5);
            }
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
  if (!d_is_valid)
  {
    // do nothing
    return n;
  }
  Node bn = n;
  TypeNode tn = n.getType();
  // If we are using sygus types, get the builtin analog of n.
  if (d_use_sygus_type)
  {
    bn = d_tds->sygusToBuiltin(n);
    d_builtin_to_sygus[tn][bn] = n;
  }
  // cache based on the (original) type of n
  Node res = d_trie[tn].add(bn, this, 0, d_samples.size(), forceKeep);
  // If we are using sygus types, map back to an original.
  // Notice that d_builtin_to_sygus is not necessarily bijective.
  if (d_use_sygus_type)
  {
    std::map<Node, Node>& bts = d_builtin_to_sygus[tn];
    Assert(bts.find(res) != bts.end());
    res = res != bn ? bts[res] : n;
  }
  return res;
}

bool SygusSampler::isContiguous(Node n)
{
  // compute free variables in n
  std::vector<Node> fvs;
  computeFreeVariables(n, fvs);
  // compute contiguous condition
  for (const std::pair<const unsigned, std::vector<Node> >& p : d_type_vars)
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

bool SygusSampler::isOrdered(Node n) { return checkVariables(n, true, false); }

bool SygusSampler::isLinear(Node n) { return checkVariables(n, false, true); }

bool SygusSampler::checkVariables(Node n, bool checkOrder, bool checkLinear)
{
  // compute free variables in n for each type
  std::map<unsigned, std::vector<Node> > fvs;

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
          if (checkOrder)
          {
            unsigned tnid = d_type_ids[cur];
            // if this variable is out of order
            if (itv->second != fvs[tnid].size())
            {
              return false;
            }
            fvs[tnid].push_back(cur);
          }
          if (checkLinear)
          {
            if (expr::hasSubtermMulti(n, cur))
            {
              return false;
            }
          }
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

bool SygusSampler::containsFreeVariables(Node a, Node b, bool strict)
{
  // compute free variables in a
  std::vector<Node> fvs;
  computeFreeVariables(a, fvs);
  std::vector<Node> fv_found;

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
        else if (strict)
        {
          if (fv_found.size() + 1 == fvs.size())
          {
            return false;
          }
          // cur should only be visited once
          Assert(std::find(fv_found.begin(), fv_found.end(), cur)
                 == fv_found.end());
          fv_found.push_back(cur);
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

void SygusSampler::getVariables(std::vector<Node>& vars) const
{
  vars.insert(vars.end(), d_vars.begin(), d_vars.end());
}

void SygusSampler::getSamplePoint(unsigned index,
                                  std::vector<Node>& pt)
{
  Assert(index < d_samples.size());
  std::vector<Node>& spt = d_samples[index];
  pt.insert(pt.end(), spt.begin(), spt.end());
}

void SygusSampler::addSamplePoint(std::vector<Node>& pt)
{
  Assert(pt.size() == d_vars.size());
  d_samples.push_back(pt);
}

Node SygusSampler::evaluate(Node n, unsigned index)
{
  Assert(index < d_samples.size());
  // do beta-reductions in n first
  n = Rewriter::rewrite(n);
  // use efficient rewrite for substitution + rewrite
  Node ev = d_eval.eval(n, d_vars, d_samples[index]);
  Trace("sygus-sample-ev") << "Evaluate ( " << n << ", " << index << " ) -> ";
  if (!ev.isNull())
  {
    Trace("sygus-sample-ev") << ev << std::endl;
    return ev;
  }
  Trace("sygus-sample-ev") << "null" << std::endl;
  Trace("sygus-sample-ev") << "Rewrite -> ";
  // substitution + rewrite
  std::vector<Node>& pt = d_samples[index];
  ev = n.substitute(d_vars.begin(), d_vars.end(), pt.begin(), pt.end());
  ev = Rewriter::rewrite(ev);
  Trace("sygus-sample-ev") << ev << std::endl;
  return ev;
}

int SygusSampler::getDiffSamplePointIndex(Node a, Node b)
{
  for (unsigned i = 0, nsamp = d_samples.size(); i < nsamp; i++)
  {
    Node ae = evaluate(a, i);
    Node be = evaluate(b, i);
    if (ae != be)
    {
      return i;
    }
  }
  return -1;
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
    return nm->mkConst(Sampler::pickBvUniform(sz));
  }
  else if (tn.isFloatingPoint())
  {
    unsigned e = tn.getFloatingPointExponentSize();
    unsigned s = tn.getFloatingPointSignificandSize();
    return nm->mkConst(options::sygusSampleFpUniform()
                           ? Sampler::pickFpUniform(e, s)
                           : Sampler::pickFpBiased(e, s));
  }
  else if (tn.isString() || tn.isInteger())
  {
    // if string, determine the alphabet
    if (tn.isString() && d_rstring_alphabet.empty())
    {
      Trace("sygus-sample-str-alpha")
          << "Setting string alphabet..." << std::endl;
      std::unordered_set<unsigned> alphas;
      for (const std::pair<const Node, std::vector<TypeNode> >& c :
           d_const_sygus_types)
      {
        if (c.first.getType().isString())
        {
          Trace("sygus-sample-str-alpha")
              << "...have constant " << c.first << std::endl;
          Assert(c.first.isConst());
          std::vector<unsigned> svec = c.first.getConst<String>().getVec();
          for (unsigned ch : svec)
          {
            alphas.insert(ch);
          }
        }
      }
      // can limit to 1 extra characters beyond those in the grammar (2 if
      // there are none in the grammar)
      unsigned num_fresh_char = alphas.empty() ? 2 : 1;
      unsigned fresh_char = 0;
      for (unsigned i = 0; i < num_fresh_char; i++)
      {
        while (alphas.find(fresh_char) != alphas.end())
        {
          fresh_char++;
        }
        alphas.insert(fresh_char);
      }
      Trace("sygus-sample-str-alpha")
          << "Sygus sampler: limit strings alphabet to : " << std::endl
          << " ";
      for (unsigned ch : alphas)
      {
        d_rstring_alphabet.push_back(ch);
        Trace("sygus-sample-str-alpha") << " \\u" << ch;
      }
      Trace("sygus-sample-str-alpha") << std::endl;
    }

    std::vector<unsigned> vec;
    double ext_freq = .5;
    unsigned base = tn.isString() ? d_rstring_alphabet.size() : 10;
    while (Random::getRandom().pickWithProb(ext_freq))
    {
      // add a digit
      unsigned digit = Random::getRandom().pick(0, base - 1);
      if (tn.isString())
      {
        digit = d_rstring_alphabet[digit];
      }
      vec.push_back(digit);
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
      Rational rr = r.getConst<Rational>();
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
  // default: use type enumerator
  unsigned counter = 0;
  while (Random::getRandom().pickWithProb(0.5))
  {
    counter++;
  }
  Node ret = d_tenum.getEnumerateTerm(tn, counter);
  if (ret.isNull())
  {
    // beyond bounds, return the first
    ret = d_tenum.getEnumerateTerm(tn, 0);
  }
  return ret;
}

Node SygusSampler::getSygusRandomValue(TypeNode tn,
                                       double rchance,
                                       double rinc,
                                       unsigned depth)
{
  if (!tn.isDatatype())
  {
    return getRandomValue(tn);
  }
  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    return getRandomValue(tn);
  }
  Assert(d_rvalue_cindices.find(tn) != d_rvalue_cindices.end());
  Trace("sygus-sample-grammar")
      << "Sygus random value " << tn << ", depth = " << depth
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
  Trace("sygus-sample-grammar")
      << "Random index 0..." << ncons << " was : " << index << std::endl;
  if (index < ncons)
  {
    Trace("sygus-sample-grammar")
        << "Recurse constructor index #" << index << std::endl;
    unsigned cindex = cindices[index];
    Assert(cindex < dt.getNumConstructors());
    const DTypeConstructor& dtc = dt[cindex];
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
      Trace("sygus-sample-grammar")
          << "  child #" << i << " : " << c << std::endl;
      pre[i] = c;
    }
    if (success)
    {
      Trace("sygus-sample-grammar") << "mkGeneric" << std::endl;
      Node ret = d_tds->mkGeneric(dt, cindex, pre);
      Trace("sygus-sample-grammar") << "...returned " << ret << std::endl;
      ret = Rewriter::rewrite(ret);
      Trace("sygus-sample-grammar") << "...after rewrite " << ret << std::endl;
      // A rare case where we generate a non-constant value from constant
      // leaves is (/ n 0).
      if(ret.isConst())
      {
        return ret;
      }
    }
  }
  Trace("sygus-sample-grammar") << "...resort to random value" << std::endl;
  // if we did not generate based on the grammar, pick a random value
  return getRandomValue(dt.getSygusType());
}

// recursion depth bounded by number of types in grammar (small)
void SygusSampler::registerSygusType(TypeNode tn)
{
  if (d_rvalue_cindices.find(tn) == d_rvalue_cindices.end())
  {
    d_rvalue_cindices[tn].clear();
    if (!tn.isDatatype())
    {
      return;
    }
    const DType& dt = tn.getDType();
    if (!dt.isSygus())
    {
      return;
    }
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DTypeConstructor& dtc = dt[i];
      Node sop = dtc.getSygusOp();
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
          if (sop.isConst())
          {
            d_const_sygus_types[sop].push_back(tn);
          }
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

void SygusSampler::checkEquivalent(Node bv, Node bvr)
{
  Trace("sygus-rr-verify") << "Testing rewrite rule " << bv << " ---> " << bvr
                           << std::endl;

  // see if they evaluate to same thing on all sample points
  bool ptDisequal = false;
  bool ptDisequalConst = false;
  unsigned pt_index = 0;
  Node bve, bvre;
  for (unsigned i = 0, npoints = getNumSamplePoints(); i < npoints; i++)
  {
    bve = evaluate(bv, i);
    bvre = evaluate(bvr, i);
    if (bve != bvre)
    {
      ptDisequal = true;
      pt_index = i;
      if (bve.isConst() && bvre.isConst())
      {
        ptDisequalConst = true;
        break;
      }
    }
  }
  // bv and bvr should be equivalent under examples
  if (ptDisequal)
  {
    std::vector<Node> vars;
    getVariables(vars);
    std::vector<Node> pt;
    getSamplePoint(pt_index, pt);
    Assert(vars.size() == pt.size());
    std::stringstream ptOut;
    for (unsigned i = 0, size = pt.size(); i < size; i++)
    {
      ptOut << "  " << vars[i] << " -> " << pt[i] << std::endl;
    }
    if (!ptDisequalConst)
    {
      Notice() << "Warning: " << bv << " and " << bvr
               << " evaluate to different (non-constant) values on point:"
               << std::endl;
      Notice() << ptOut.str();
      return;
    }
    // we have detected unsoundness in the rewriter
    Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
    std::ostream* out = nodeManagerOptions.getOut();
    (*out) << "(unsound-rewrite " << bv << " " << bvr << ")" << std::endl;
    // debugging information
    (*out) << "Terms are not equivalent for : " << std::endl;
    (*out) << ptOut.str();
    Assert(bve != bvre);
    (*out) << "where they evaluate to " << bve << " and " << bvre << std::endl;

    if (options::sygusRewVerifyAbort())
    {
      AlwaysAssert(false)
          << "--sygus-rr-verify detected unsoundness in the rewriter!";
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
