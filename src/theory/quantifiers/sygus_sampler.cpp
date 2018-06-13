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

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/lazy_trie.h"
#include "util/bitvector.h"
#include "util/random.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusSampler::SygusSampler()
    : d_tds(nullptr), d_use_sygus_type(false), d_is_valid(false)
{
}

void SygusSampler::initialize(TypeNode tn,
                              std::vector<Node>& vars,
                              unsigned nsamples)
{
  d_tds = nullptr;
  d_use_sygus_type = false;
  d_is_valid = true;
  d_tn = tn;
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
  const Datatype& dt = static_cast<DatatypeType>(d_ftn.toType()).getDatatype();
  Assert(dt.isSygus());
  d_tn = TypeNode::fromType(dt.getSygusType());

  Trace("sygus-sample") << "Register sampler for " << f << std::endl;

  d_vars.clear();
  d_type_vars.clear();
  d_var_index.clear();
  d_type_vars.clear();
  d_rvalue_cindices.clear();
  d_rvalue_null_cindices.clear();
  d_var_sygus_types.clear();
  // get the sygus variable list
  Node var_list = Node::fromExpr(dt.getSygusVarList());
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
    Node bn = n;
    // if this is a sygus type, get its builtin analog
    if (d_use_sygus_type)
    {
      Assert(!d_ftn.isNull());
      bn = d_tds->sygusToBuiltin(n);
      Assert(d_builtin_to_sygus.find(bn) == d_builtin_to_sygus.end()
             || d_builtin_to_sygus[bn] == n);
      d_builtin_to_sygus[bn] = n;
    }
    Assert(bn.getType() == d_tn);
    Node res = d_trie.add(bn, this, 0, d_samples.size(), forceKeep);
    if (d_use_sygus_type)
    {
      Assert(d_builtin_to_sygus.find(res) != d_builtin_to_sygus.end());
      res = res != bn ? d_builtin_to_sygus[res] : n;
    }
    return res;
  }
  return n;
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

bool SygusSampler::isOrdered(Node n)
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
          unsigned tnid = d_type_ids[cur];
          // if this variable is out of order
          if (itv->second != fvs[tnid].size())
          {
            return false;
          }
          fvs[tnid].push_back(cur);
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
                                  std::vector<Node>& vars,
                                  std::vector<Node>& pt)
{
  Assert(index < d_samples.size());
  vars.insert(vars.end(), d_vars.begin(), d_vars.end());
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
  // just a substitution
  std::vector<Node>& pt = d_samples[index];
  Node ev = n.substitute(d_vars.begin(), d_vars.end(), pt.begin(), pt.end());
  Trace("sygus-sample-ev-debug") << "Rewrite : " << ev << std::endl;
  ev = Rewriter::rewrite(ev);
  Trace("sygus-sample-ev") << "( " << n << ", " << index << " ) -> " << ev
                           << std::endl;
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
    std::stringstream ss;
    for (unsigned i = 0; i < sz; i++)
    {
      ss << (Random::getRandom().pickWithProb(0.5) ? "1" : "0");
    }
    return nm->mkConst(BitVector(ss.str(), 2));
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
        Trace("sygus-sample-str-alpha")
            << " \"" << String::convertUnsignedIntToChar(ch) << "\"";
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
  if (!tn.isDatatype())
  {
    return getRandomValue(tn);
  }
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
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
    if (!tn.isDatatype())
    {
      return;
    }
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    if (!dt.isSygus())
    {
      return;
    }
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

SygusSamplerExt::SygusSamplerExt() : d_ssenm(*this) {}

void SygusSamplerExt::initializeSygusExt(QuantifiersEngine* qe,
                                         Node f,
                                         unsigned nsamples,
                                         bool useSygusType)
{
  SygusSampler::initializeSygus(
      qe->getTermDatabaseSygus(), f, nsamples, useSygusType);

  // initialize the dynamic rewriter
  std::stringstream ss;
  ss << f;
  if (options::sygusRewSynthFilterCong())
  {
    d_drewrite =
        std::unique_ptr<DynamicRewriter>(new DynamicRewriter(ss.str(), qe));
  }
  d_pairs.clear();
  d_match_trie.clear();
}

Node SygusSamplerExt::registerTerm(Node n, bool forceKeep)
{
  Node eq_n = SygusSampler::registerTerm(n, forceKeep);
  if (eq_n == n)
  {
    // this is a unique term
    return n;
  }
  Node bn = n;
  Node beq_n = eq_n;
  if (d_use_sygus_type)
  {
    bn = d_tds->sygusToBuiltin(n);
    beq_n = d_tds->sygusToBuiltin(eq_n);
  }
  Trace("sygus-synth-rr") << "sygusSampleExt : " << bn << "..." << beq_n
                          << std::endl;
  // whether we will keep this pair
  bool keep = true;

  // ----- check ordering redundancy
  if (options::sygusRewSynthFilterOrder())
  {
    bool nor = isOrdered(bn);
    bool eqor = isOrdered(beq_n);
    Trace("sygus-synth-rr-debug") << "Ordered? : " << nor << " " << eqor
                                  << std::endl;
    if (eqor || nor)
    {
      // if only one is ordered, then we require that the ordered one's
      // variables cannot be a strict subset of the variables of the other.
      if (!eqor)
      {
        if (containsFreeVariables(beq_n, bn, true))
        {
          keep = false;
        }
        else
        {
          // if the previous value stored was unordered, but n is
          // ordered, we prefer n. Thus, we force its addition to the
          // sampler database.
          SygusSampler::registerTerm(n, true);
        }
      }
      else if (!nor)
      {
        keep = !containsFreeVariables(bn, beq_n, true);
      }
    }
    else
    {
      keep = false;
    }
    if (!keep)
    {
      Trace("sygus-synth-rr") << "...redundant (unordered)" << std::endl;
    }
  }

  // ----- check rewriting redundancy
  if (keep && d_drewrite != nullptr)
  {
    Trace("sygus-synth-rr-debug") << "Check equal rewrite pair..." << std::endl;
    if (d_drewrite->areEqual(bn, beq_n))
    {
      // must be unique according to the dynamic rewriter
      Trace("sygus-synth-rr") << "...redundant (rewritable)" << std::endl;
      keep = false;
    }
  }

  if (options::sygusRewSynthFilterMatch())
  {
    // ----- check matchable
    // check whether the pair is matchable with a previous one
    d_curr_pair_rhs = beq_n;
    Trace("sse-match") << "SSE check matches : " << bn << " [rhs = " << beq_n
                       << "]..." << std::endl;
    if (!d_match_trie.getMatches(bn, &d_ssenm))
    {
      keep = false;
      Trace("sygus-synth-rr") << "...redundant (matchable)" << std::endl;
      // regardless, would help to remember it
      registerRelevantPair(n, eq_n);
    }
  }

  if (keep)
  {
    return eq_n;
  }
  if (Trace.isOn("sygus-rr-filter"))
  {
    Printer* p = Printer::getPrinter(options::outputLanguage());
    std::stringstream ss;
    ss << "(redundant-rewrite ";
    p->toStreamSygus(ss, n);
    ss << " ";
    p->toStreamSygus(ss, eq_n);
    ss << ")";
    Trace("sygus-rr-filter") << ss.str() << std::endl;
  }
  return Node::null();
}

void SygusSamplerExt::registerRelevantPair(Node n, Node eq_n)
{
  Node bn = n;
  Node beq_n = eq_n;
  if (d_use_sygus_type)
  {
    bn = d_tds->sygusToBuiltin(n);
    beq_n = d_tds->sygusToBuiltin(eq_n);
  }
  // ----- check rewriting redundancy
  if (d_drewrite != nullptr)
  {
    Trace("sygus-synth-rr-debug") << "Add rewrite pair..." << std::endl;
    Assert(!d_drewrite->areEqual(bn, beq_n));
    d_drewrite->addRewrite(bn, beq_n);
  }
  if (options::sygusRewSynthFilterMatch())
  {
    // add to match information
    for (unsigned r = 0; r < 2; r++)
    {
      Node t = r == 0 ? bn : beq_n;
      Node to = r == 0 ? beq_n : bn;
      // insert in match trie if first time
      if (d_pairs.find(t) == d_pairs.end())
      {
        Trace("sse-match") << "SSE add term : " << t << std::endl;
        d_match_trie.addTerm(t);
      }
      d_pairs[t].insert(to);
    }
  }
}

bool SygusSamplerExt::notify(Node s,
                             Node n,
                             std::vector<Node>& vars,
                             std::vector<Node>& subs)
{
  Assert(!d_curr_pair_rhs.isNull());
  std::map<Node, std::unordered_set<Node, NodeHashFunction> >::iterator it =
      d_pairs.find(n);
  if (Trace.isOn("sse-match"))
  {
    Trace("sse-match") << "  " << s << " matches " << n
                       << " under:" << std::endl;
    for (unsigned i = 0, size = vars.size(); i < size; i++)
    {
      Trace("sse-match") << "    " << vars[i] << " -> " << subs[i] << std::endl;
    }
  }
  Assert(it != d_pairs.end());
  for (const Node& nr : it->second)
  {
    Node nrs =
        nr.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    bool areEqual = (nrs == d_curr_pair_rhs);
    if (!areEqual && d_drewrite != nullptr)
    {
      // if dynamic rewriter is available, consult it
      areEqual = d_drewrite->areEqual(nrs, d_curr_pair_rhs);
    }
    if (areEqual)
    {
      Trace("sse-match") << "*** Match, current pair: " << std::endl;
      Trace("sse-match") << "  (" << s << ", " << d_curr_pair_rhs << ")"
                         << std::endl;
      Trace("sse-match") << "is an instance of previous pair:" << std::endl;
      Trace("sse-match") << "  (" << n << ", " << nr << ")" << std::endl;
      return false;
    }
  }
  return true;
}

bool MatchTrie::getMatches(Node n, NotifyMatch* ntm)
{
  std::vector<Node> vars;
  std::vector<Node> subs;
  std::map<Node, Node> smap;

  std::vector<std::vector<Node> > visit;
  std::vector<MatchTrie*> visit_trie;
  std::vector<int> visit_var_index;
  std::vector<bool> visit_bound_var;

  visit.push_back(std::vector<Node>{n});
  visit_trie.push_back(this);
  visit_var_index.push_back(-1);
  visit_bound_var.push_back(false);
  while (!visit.empty())
  {
    std::vector<Node> cvisit = visit.back();
    MatchTrie* curr = visit_trie.back();
    if (cvisit.empty())
    {
      Assert(n
             == curr->d_data.substitute(
                    vars.begin(), vars.end(), subs.begin(), subs.end()));
      Trace("sse-match-debug") << "notify : " << curr->d_data << std::endl;
      if (!ntm->notify(n, curr->d_data, vars, subs))
      {
        return false;
      }
      visit.pop_back();
      visit_trie.pop_back();
      visit_var_index.pop_back();
      visit_bound_var.pop_back();
    }
    else
    {
      Node cn = cvisit.back();
      Trace("sse-match-debug")
          << "traverse : " << cn << " at depth " << visit.size() << std::endl;
      unsigned index = visit.size() - 1;
      int vindex = visit_var_index[index];
      if (vindex == -1)
      {
        if (!cn.isVar())
        {
          Node op = cn.hasOperator() ? cn.getOperator() : cn;
          unsigned nchild = cn.hasOperator() ? cn.getNumChildren() : 0;
          std::map<unsigned, MatchTrie>::iterator itu =
              curr->d_children[op].find(nchild);
          if (itu != curr->d_children[op].end())
          {
            // recurse on the operator or self
            cvisit.pop_back();
            if (cn.hasOperator())
            {
              for (const Node& cnc : cn)
              {
                cvisit.push_back(cnc);
              }
            }
            Trace("sse-match-debug") << "recurse op : " << op << std::endl;
            visit.push_back(cvisit);
            visit_trie.push_back(&itu->second);
            visit_var_index.push_back(-1);
            visit_bound_var.push_back(false);
          }
        }
        visit_var_index[index]++;
      }
      else
      {
        // clean up if we previously bound a variable
        if (visit_bound_var[index])
        {
          Assert(!vars.empty());
          smap.erase(vars.back());
          vars.pop_back();
          subs.pop_back();
          visit_bound_var[index] = false;
        }

        if (vindex == static_cast<int>(curr->d_vars.size()))
        {
          Trace("sse-match-debug")
              << "finished checking " << curr->d_vars.size()
              << " variables at depth " << visit.size() << std::endl;
          // finished
          visit.pop_back();
          visit_trie.pop_back();
          visit_var_index.pop_back();
          visit_bound_var.pop_back();
        }
        else
        {
          Trace("sse-match-debug") << "check variable #" << vindex
                                   << " at depth " << visit.size() << std::endl;
          Assert(vindex < static_cast<int>(curr->d_vars.size()));
          // recurse on variable?
          Node var = curr->d_vars[vindex];
          bool recurse = true;
          // check if it is already bound
          std::map<Node, Node>::iterator its = smap.find(var);
          if (its != smap.end())
          {
            if (its->second != cn)
            {
              recurse = false;
            }
          }
          else
          {
            vars.push_back(var);
            subs.push_back(cn);
            smap[var] = cn;
            visit_bound_var[index] = true;
          }
          if (recurse)
          {
            Trace("sse-match-debug") << "recurse var : " << var << std::endl;
            cvisit.pop_back();
            visit.push_back(cvisit);
            visit_trie.push_back(&curr->d_children[var][0]);
            visit_var_index.push_back(-1);
            visit_bound_var.push_back(false);
          }
          visit_var_index[index]++;
        }
      }
    }
  }
  return true;
}

void MatchTrie::addTerm(Node n)
{
  std::vector<Node> visit;
  visit.push_back(n);
  MatchTrie* curr = this;
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    if (cn.hasOperator())
    {
      curr = &(curr->d_children[cn.getOperator()][cn.getNumChildren()]);
      for (const Node& cnc : cn)
      {
        visit.push_back(cnc);
      }
    }
    else
    {
      if (cn.isVar()
          && std::find(curr->d_vars.begin(), curr->d_vars.end(), cn)
                 == curr->d_vars.end())
      {
        curr->d_vars.push_back(cn);
      }
      curr = &(curr->d_children[cn][0]);
    }
  }
  curr->d_data = n;
}

void MatchTrie::clear()
{
  d_children.clear();
  d_vars.clear();
  d_data = Node::null();
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
