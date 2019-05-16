/*********************                                                        */
/*! \file candidate_rewrite_filter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements techniques for candidate rewrite rule filtering, which
 ** filters the output of --sygus-rr-synth. The classes in this file implement
 ** filtering based on congruence, variable ordering, and matching.
 **/

#include "theory/quantifiers/candidate_rewrite_filter.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

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
      Trace("crf-match-debug") << "notify : " << curr->d_data << std::endl;
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
      Trace("crf-match-debug") << "traverse : " << cn << " at depth "
                               << visit.size() << std::endl;
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
            Trace("crf-match-debug") << "recurse op : " << op << std::endl;
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
          Trace("crf-match-debug")
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
          Trace("crf-match-debug") << "check variable #" << vindex
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
            Trace("crf-match-debug") << "recurse var : " << var << std::endl;
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
  Assert(!n.isNull());
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

// the number of d_drewrite objects we have allocated (to avoid name conflicts)
static unsigned drewrite_counter = 0;

CandidateRewriteFilter::CandidateRewriteFilter()
    : d_ss(nullptr),
      d_tds(nullptr),
      d_use_sygus_type(false),
      d_drewrite(nullptr),
      d_ssenm(*this)
{
}

void CandidateRewriteFilter::initialize(SygusSampler* ss,
                                        TermDbSygus* tds,
                                        bool useSygusType)
{
  d_ss = ss;
  d_use_sygus_type = useSygusType;
  d_tds = tds;
  // initialize members of this class
  d_match_trie.clear();
  d_pairs.clear();
  // (re)initialize the dynamic rewriter
  std::stringstream ssn;
  ssn << "_dyn_rewriter_" << drewrite_counter;
  drewrite_counter++;
  d_drewrite = std::unique_ptr<DynamicRewriter>(
      new DynamicRewriter(ssn.str(), &d_fake_context));
}

bool CandidateRewriteFilter::filterPair(Node n, Node eq_n)
{
  Node bn = n;
  Node beq_n = eq_n;
  if (d_use_sygus_type)
  {
    bn = d_tds->sygusToBuiltin(n);
    beq_n = d_tds->sygusToBuiltin(eq_n);
  }
  Trace("cr-filter") << "crewriteFilter : " << bn << "..." << beq_n
                     << std::endl;
  // whether we will keep this pair
  bool keep = true;

  // ----- check redundancy based on variables
  if (options::sygusRewSynthFilterOrder()
      || options::sygusRewSynthFilterNonLinear())
  {
    bool nor = d_ss->checkVariables(bn,
                                    options::sygusRewSynthFilterOrder(),
                                    options::sygusRewSynthFilterNonLinear());
    bool eqor = d_ss->checkVariables(beq_n,
                                     options::sygusRewSynthFilterOrder(),
                                     options::sygusRewSynthFilterNonLinear());
    Trace("cr-filter-debug")
        << "Variables ok? : " << nor << " " << eqor << std::endl;
    if (eqor || nor)
    {
      // if only one is ordered, then we require that the ordered one's
      // variables cannot be a strict subset of the variables of the other.
      if (!eqor)
      {
        if (d_ss->containsFreeVariables(beq_n, bn, true))
        {
          keep = false;
        }
        else
        {
          // if the previous value stored was unordered, but n is
          // ordered, we prefer n. Thus, we force its addition to the
          // sampler database.
          d_ss->registerTerm(n, true);
        }
      }
      else if (!nor)
      {
        keep = !d_ss->containsFreeVariables(bn, beq_n, true);
      }
    }
    else
    {
      keep = false;
    }
    if (!keep)
    {
      Trace("cr-filter") << "...redundant (unordered)" << std::endl;
    }
  }

  // ----- check rewriting redundancy
  if (keep && options::sygusRewSynthFilterCong())
  {
    // When using sygus types, this filtering applies to the builtin versions
    // of n and eq_n. This means that we may filter out a rewrite rule for one
    // sygus type based on another, e.g. we won't report x=x+0 for both A and B
    // in:
    //   A -> x | 0 | A+A
    //   B -> x | 0 | B+B
    Trace("cr-filter-debug") << "Check equal rewrite pair..." << std::endl;
    if (d_drewrite->areEqual(bn, beq_n))
    {
      // must be unique according to the dynamic rewriter
      Trace("cr-filter") << "...redundant (rewritable)" << std::endl;
      keep = false;
    }
  }

  if (keep && options::sygusRewSynthFilterMatch())
  {
    // ----- check matchable
    // check whether the pair is matchable with a previous one
    d_curr_pair_rhs = beq_n;
    Trace("crf-match") << "CRF check matches : " << bn << " [rhs = " << beq_n
                       << "]..." << std::endl;
    Node bni = d_drewrite->toInternal(bn);
    if (!bni.isNull())
    {
      // as with congruence filtering, we cache based on the builtin type
      TypeNode tn = bn.getType();
      if (!d_match_trie[tn].getMatches(bni, &d_ssenm))
      {
        keep = false;
        Trace("cr-filter") << "...redundant (matchable)" << std::endl;
        // regardless, would help to remember it
        registerRelevantPair(n, eq_n);
      }
    }
    // if bni is null, it may involve non-first-class types that we cannot
    // reason about
  }

  if (keep)
  {
    return false;
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
  return true;
}

void CandidateRewriteFilter::registerRelevantPair(Node n, Node eq_n)
{
  Node bn = n;
  Node beq_n = eq_n;
  if (d_use_sygus_type)
  {
    bn = d_tds->sygusToBuiltin(n);
    beq_n = d_tds->sygusToBuiltin(eq_n);
  }
  // ----- check rewriting redundancy
  if (options::sygusRewSynthFilterCong())
  {
    Trace("cr-filter-debug") << "Add rewrite pair..." << std::endl;
    Assert(!d_drewrite->areEqual(bn, beq_n));
    d_drewrite->addRewrite(bn, beq_n);
  }
  if (options::sygusRewSynthFilterMatch())
  {
    // cache based on the builtin type
    TypeNode tn = bn.getType();
    // add to match information
    for (unsigned r = 0; r < 2; r++)
    {
      Node t = r == 0 ? bn : beq_n;
      Node to = r == 0 ? beq_n : bn;
      // insert in match trie if first time
      if (d_pairs.find(t) == d_pairs.end())
      {
        Trace("crf-match") << "CRF add term : " << t << std::endl;
        Node ti = d_drewrite->toInternal(t);
        if (!ti.isNull())
        {
          d_match_trie[tn].addTerm(ti);
        }
      }
      d_pairs[t].insert(to);
    }
  }
}

bool CandidateRewriteFilter::notify(Node s,
                                    Node n,
                                    std::vector<Node>& vars,
                                    std::vector<Node>& subs)
{
  Trace("crf-match-debug") << "Got : " << s << " matches " << n << std::endl;
  Assert(!d_curr_pair_rhs.isNull());
  // convert back to original forms
  s = d_drewrite->toExternal(s);
  Assert(!s.isNull());
  n = d_drewrite->toExternal(n);
  Assert(!n.isNull());
  std::map<Node, std::unordered_set<Node, NodeHashFunction> >::iterator it =
      d_pairs.find(n);
  if (Trace.isOn("crf-match"))
  {
    Trace("crf-match") << "  " << s << " matches " << n
                       << " under:" << std::endl;
    for (unsigned i = 0, size = vars.size(); i < size; i++)
    {
      Trace("crf-match") << "    " << vars[i] << " -> " << subs[i] << std::endl;
    }
  }
#ifdef CVC4_ASSERTIONS
  for (unsigned i = 0, size = vars.size(); i < size; i++)
  {
    // By using internal representation of terms, we ensure polymorphism is
    // handled correctly.
    Assert(vars[i].getType().isComparableTo(subs[i].getType()));
  }
#endif
  // must convert the inferred substitution to original form
  std::vector<Node> esubs;
  for (const Node& s : subs)
  {
    esubs.push_back(d_drewrite->toExternal(s));
  }
  Assert(it != d_pairs.end());
  for (const Node& nr : it->second)
  {
    Node nrs =
        nr.substitute(vars.begin(), vars.end(), esubs.begin(), esubs.end());
    bool areEqual = (nrs == d_curr_pair_rhs);
    if (!areEqual && options::sygusRewSynthFilterCong())
    {
      // if dynamic rewriter is available, consult it
      areEqual = d_drewrite->areEqual(nrs, d_curr_pair_rhs);
    }
    if (areEqual)
    {
      Trace("crf-match") << "*** Match, current pair: " << std::endl;
      Trace("crf-match") << "  (" << s << ", " << d_curr_pair_rhs << ")"
                         << std::endl;
      Trace("crf-match") << "is an instance of previous pair:" << std::endl;
      Trace("crf-match") << "  (" << n << ", " << nr << ")" << std::endl;
      return false;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
