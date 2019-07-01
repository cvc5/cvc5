/*********************                                                        */
/*! \file regexp_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the regular expression solver for the theory of
 ** strings.
 **
 **/

#include "theory/strings/regexp_solver.h"

#include <cmath>

#include "options/strings_options.h"
#include "theory/strings/theory_strings.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/theory_model.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

RegExpSolver::RegExpSolver(TheoryStrings& p,
                           InferenceManager& im,
                           context::Context* c,
                           context::UserContext* u)
    : d_parent(p),
      d_im(im),
      d_regexp_memberships(c),
      d_regexp_ucached(u),
      d_regexp_ccached(c),
      d_pos_memberships(c),
      d_neg_memberships(c),
      d_inter_cache(c),
      d_inter_index(c),
      d_processed_memberships(c)
{
  d_emptyString = NodeManager::currentNM()->mkConst(::CVC4::String(""));
  std::vector<Node> nvec;
  d_emptyRegexp = NodeManager::currentNM()->mkNode(REGEXP_EMPTY, nvec);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

unsigned RegExpSolver::getNumMemberships(Node n, bool isPos)
{
  if (isPos)
  {
    NodeUIntMap::const_iterator it = d_pos_memberships.find(n);
    if (it != d_pos_memberships.end())
    {
      return (*it).second;
    }
  }
  else
  {
    NodeUIntMap::const_iterator it = d_neg_memberships.find(n);
    if (it != d_neg_memberships.end())
    {
      return (*it).second;
    }
  }
  return 0;
}

Node RegExpSolver::getMembership(Node n, bool isPos, unsigned i)
{
  return isPos ? d_pos_memberships_data[n][i] : d_neg_memberships_data[n][i];
}

Node RegExpSolver::mkAnd(Node c1, Node c2)
{
  return NodeManager::currentNM()->mkNode(AND, c1, c2);
}

void RegExpSolver::check()
{
  bool addedLemma = false;
  bool changed = false;
  std::vector<Node> processed;
  std::vector<Node> cprocessed;

  Trace("regexp-debug") << "Checking Memberships ... " << std::endl;
  for (NodeUIntMap::const_iterator itr_xr = d_pos_memberships.begin();
       itr_xr != d_pos_memberships.end();
       ++itr_xr)
  {
    bool spflag = false;
    Node x = (*itr_xr).first;
    Trace("regexp-debug") << "Checking Memberships for " << x << std::endl;
    if (d_inter_index.find(x) == d_inter_index.end())
    {
      d_inter_index[x] = 0;
    }
    int cur_inter_idx = d_inter_index[x];
    unsigned n_pmem = (*itr_xr).second;
    Assert(getNumMemberships(x, true) == n_pmem);
    if (cur_inter_idx != (int)n_pmem)
    {
      if (n_pmem == 1)
      {
        d_inter_cache[x] = getMembership(x, true, 0);
        d_inter_index[x] = 1;
        Trace("regexp-debug") << "... only one choice " << std::endl;
      }
      else if (n_pmem > 1)
      {
        Node r;
        if (d_inter_cache.find(x) != d_inter_cache.end())
        {
          r = d_inter_cache[x];
        }
        if (r.isNull())
        {
          r = getMembership(x, true, 0);
          cur_inter_idx = 1;
        }

        unsigned k_start = cur_inter_idx;
        Trace("regexp-debug") << "... staring from : " << cur_inter_idx
                              << ", we have " << n_pmem << std::endl;
        for (unsigned k = k_start; k < n_pmem; k++)
        {
          Node r2 = getMembership(x, true, k);
          r = d_regexp_opr.intersect(r, r2, spflag);
          if (spflag)
          {
            break;
          }
          else if (r == d_emptyRegexp)
          {
            std::vector<Node> vec_nodes;
            for (unsigned kk = 0; kk <= k; kk++)
            {
              Node rr = getMembership(x, true, kk);
              Node n =
                  NodeManager::currentNM()->mkNode(STRING_IN_REGEXP, x, rr);
              vec_nodes.push_back(n);
            }
            Node conc;
            d_im.sendInference(vec_nodes, conc, "INTERSECT CONFLICT", true);
            addedLemma = true;
            break;
          }
          if (d_im.hasConflict())
          {
            break;
          }
        }
        // updates
        if (!d_im.hasConflict() && !spflag)
        {
          d_inter_cache[x] = r;
          d_inter_index[x] = (int)n_pmem;
        }
      }
    }
  }

  Trace("regexp-debug")
      << "... No Intersect Conflict in Memberships, addedLemma: " << addedLemma
      << std::endl;
  if (!addedLemma)
  {
    NodeManager* nm = NodeManager::currentNM();
    // representatives of strings that are the LHS of positive memberships that
    // we unfolded
    std::unordered_set<Node, NodeHashFunction> repUnfold;
    // check positive (e=0), then negative (e=1) memberships
    for (unsigned e = 0; e < 2; e++)
    {
      for (const Node& assertion : d_regexp_memberships)
      {
        // check regular expression membership
        Trace("regexp-debug")
            << "Check : " << assertion << " "
            << (d_regexp_ucached.find(assertion) == d_regexp_ucached.end())
            << " "
            << (d_regexp_ccached.find(assertion) == d_regexp_ccached.end())
            << std::endl;
        if (d_regexp_ucached.find(assertion) != d_regexp_ucached.end()
            || d_regexp_ccached.find(assertion) != d_regexp_ccached.end())
        {
          continue;
        }
        Trace("strings-regexp")
            << "We have regular expression assertion : " << assertion
            << std::endl;
        Node atom = assertion.getKind() == NOT ? assertion[0] : assertion;
        bool polarity = assertion.getKind() != NOT;
        if (polarity != (e == 0))
        {
          continue;
        }
        bool flag = true;
        Node x = atom[0];
        Node r = atom[1];
        std::vector<Node> rnfexp;

        if (!x.isConst())
        {
          x = d_parent.getNormalString(x, rnfexp);
          changed = true;
        }
        if (!d_regexp_opr.checkConstRegExp(r))
        {
          r = getNormalSymRegExp(r, rnfexp);
          changed = true;
        }
        Trace("strings-regexp-nf") << "Term " << atom << " is normalized to "
                                   << x << " IN " << r << std::endl;
        if (changed)
        {
          Node tmp = Rewriter::rewrite(nm->mkNode(STRING_IN_REGEXP, x, r));
          if (!polarity)
          {
            tmp = tmp.negate();
          }
          if (tmp == d_true)
          {
            d_regexp_ccached.insert(assertion);
            continue;
          }
          else if (tmp == d_false)
          {
            std::vector<Node> exp_n;
            exp_n.push_back(assertion);
            Node conc = Node::null();
            d_im.sendInference(rnfexp, exp_n, conc, "REGEXP NF Conflict");
            addedLemma = true;
            break;
          }
        }
        if (e == 1 && repUnfold.find(x) != repUnfold.end())
        {
          // do not unfold negative memberships of strings that have new
          // positive unfoldings. For example:
          //   x in ("A")* ^ NOT x in ("B")*
          // We unfold x = "A" ++ x' only. The intution here is that positive
          // unfoldings lead to stronger constraints (equalities are stronger
          // than disequalities), and are easier to check.
          continue;
        }
        if (polarity)
        {
          flag = checkPDerivative(x, r, atom, addedLemma, rnfexp);
        }
        else
        {
          if (!options::stringExp())
          {
            throw LogicException(
                "Strings Incomplete (due to Negative Membership) by default, "
                "try --strings-exp option.");
          }
        }
        if (flag)
        {
          // check if the term is atomic
          Node xr = d_parent.getRepresentative(x);
          Trace("strings-regexp")
              << "Unroll/simplify membership of atomic term " << xr
              << std::endl;
          // if so, do simple unrolling
          std::vector<Node> nvec;
          if (nvec.empty())
          {
            d_regexp_opr.simplify(atom, nvec, polarity);
          }
          std::vector<Node> exp_n;
          exp_n.push_back(assertion);
          Node conc = nvec.size() == 1 ? nvec[0] : nm->mkNode(AND, nvec);
          conc = Rewriter::rewrite(conc);
          d_im.sendInference(rnfexp, exp_n, conc, "REGEXP_Unfold");
          addedLemma = true;
          if (changed)
          {
            cprocessed.push_back(assertion);
          }
          else
          {
            processed.push_back(assertion);
          }
          if (e == 0)
          {
            // Remember that we have unfolded a membership for x
            // notice that we only do this here, after we have definitely
            // added a lemma.
            repUnfold.insert(x);
          }
        }
        if (d_im.hasConflict())
        {
          break;
        }
      }
    }
  }
  if (addedLemma)
  {
    if (!d_im.hasConflict())
    {
      for (unsigned i = 0; i < processed.size(); i++)
      {
        Trace("strings-regexp")
            << "...add " << processed[i] << " to u-cache." << std::endl;
        d_regexp_ucached.insert(processed[i]);
      }
      for (unsigned i = 0; i < cprocessed.size(); i++)
      {
        Trace("strings-regexp")
            << "...add " << cprocessed[i] << " to c-cache." << std::endl;
        d_regexp_ccached.insert(cprocessed[i]);
      }
    }
  }
}

bool RegExpSolver::checkPDerivative(
    Node x, Node r, Node atom, bool& addedLemma, std::vector<Node>& nf_exp)
{
  if (d_parent.areEqual(x, d_emptyString))
  {
    Node exp;
    switch (d_regexp_opr.delta(r, exp))
    {
      case 0:
      {
        std::vector<Node> exp_n;
        exp_n.push_back(atom);
        exp_n.push_back(x.eqNode(d_emptyString));
        d_im.sendInference(nf_exp, exp_n, exp, "RegExp Delta");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
      case 1:
      {
        d_regexp_ccached.insert(atom);
        break;
      }
      case 2:
      {
        std::vector<Node> exp_n;
        exp_n.push_back(atom);
        exp_n.push_back(x.eqNode(d_emptyString));
        Node conc;
        d_im.sendInference(nf_exp, exp_n, conc, "RegExp Delta CONFLICT");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
      default:
        // Impossible
        break;
    }
  }
  else
  {
    if (deriveRegExp(x, r, atom, nf_exp))
    {
      addedLemma = true;
      d_regexp_ccached.insert(atom);
      return false;
    }
  }
  return true;
}

CVC4::String RegExpSolver::getHeadConst(Node x)
{
  if (x.isConst())
  {
    return x.getConst<String>();
  }
  else if (x.getKind() == STRING_CONCAT)
  {
    if (x[0].isConst())
    {
      return x[0].getConst<String>();
    }
  }
  return d_emptyString.getConst<String>();
}

bool RegExpSolver::deriveRegExp(Node x,
                                Node r,
                                Node atom,
                                std::vector<Node>& ant)
{
  Assert(x != d_emptyString);
  Trace("regexp-derive") << "RegExpSolver::deriveRegExp: x=" << x
                         << ", r= " << r << std::endl;
  CVC4::String s = getHeadConst(x);
  if (!s.isEmptyString() && d_regexp_opr.checkConstRegExp(r))
  {
    Node conc = Node::null();
    Node dc = r;
    bool flag = true;
    for (unsigned i = 0; i < s.size(); ++i)
    {
      CVC4::String c = s.substr(i, 1);
      Node dc2;
      int rt = d_regexp_opr.derivativeS(dc, c, dc2);
      dc = dc2;
      if (rt == 2)
      {
        // CONFLICT
        flag = false;
        break;
      }
    }
    // send lemma
    if (flag)
    {
      if (x.isConst())
      {
        Assert(false,
               "Impossible: RegExpSolver::deriveRegExp: const string in const "
               "regular expression.");
        return false;
      }
      else
      {
        Assert(x.getKind() == STRING_CONCAT);
        std::vector<Node> vec_nodes;
        for (unsigned int i = 1; i < x.getNumChildren(); ++i)
        {
          vec_nodes.push_back(x[i]);
        }
        Node left = TheoryStringsRewriter::mkConcat(STRING_CONCAT, vec_nodes);
        left = Rewriter::rewrite(left);
        conc = NodeManager::currentNM()->mkNode(STRING_IN_REGEXP, left, dc);
      }
    }
    std::vector<Node> exp_n;
    exp_n.push_back(atom);
    d_im.sendInference(ant, exp_n, conc, "RegExp-Derive");
    return true;
  }
  return false;
}

void RegExpSolver::addMembership(Node assertion)
{
  bool polarity = assertion.getKind() != NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Node x = atom[0];
  Node r = atom[1];
  if (polarity)
  {
    unsigned index = 0;
    NodeUIntMap::const_iterator it = d_pos_memberships.find(x);
    if (it != d_pos_memberships.end())
    {
      index = (*it).second;
      for (unsigned k = 0; k < index; k++)
      {
        if (k < d_pos_memberships_data[x].size())
        {
          if (d_pos_memberships_data[x][k] == r)
          {
            return;
          }
        }
        else
        {
          break;
        }
      }
    }
    d_pos_memberships[x] = index + 1;
    if (index < d_pos_memberships_data[x].size())
    {
      d_pos_memberships_data[x][index] = r;
    }
    else
    {
      d_pos_memberships_data[x].push_back(r);
    }
  }
  else if (!options::stringIgnNegMembership())
  {
    unsigned index = 0;
    NodeUIntMap::const_iterator it = d_neg_memberships.find(x);
    if (it != d_neg_memberships.end())
    {
      index = (*it).second;
      for (unsigned k = 0; k < index; k++)
      {
        if (k < d_neg_memberships_data[x].size())
        {
          if (d_neg_memberships_data[x][k] == r)
          {
            return;
          }
        }
        else
        {
          break;
        }
      }
    }
    d_neg_memberships[x] = index + 1;
    if (index < d_neg_memberships_data[x].size())
    {
      d_neg_memberships_data[x][index] = r;
    }
    else
    {
      d_neg_memberships_data[x].push_back(r);
    }
  }
  // old
  if (polarity || !options::stringIgnNegMembership())
  {
    d_regexp_memberships.push_back(assertion);
  }
}

Node RegExpSolver::getNormalSymRegExp(Node r, std::vector<Node>& nf_exp)
{
  Node ret = r;
  switch (r.getKind())
  {
    case REGEXP_EMPTY:
    case REGEXP_SIGMA: break;
    case STRING_TO_REGEXP:
    {
      if (!r[0].isConst())
      {
        Node tmp = d_parent.getNormalString(r[0], nf_exp);
        if (tmp != r[0])
        {
          ret = NodeManager::currentNM()->mkNode(STRING_TO_REGEXP, tmp);
        }
      }
      break;
    }
    case REGEXP_CONCAT:
    case REGEXP_UNION:
    case REGEXP_INTER:
    case REGEXP_STAR:
    {
      std::vector<Node> vec_nodes;
      for (const Node& cr : r)
      {
        vec_nodes.push_back(getNormalSymRegExp(cr, nf_exp));
      }
      ret = Rewriter::rewrite(
          NodeManager::currentNM()->mkNode(r.getKind(), vec_nodes));
      break;
    }
    default:
    {
      Trace("strings-error") << "Unsupported term: " << r
                             << " in normalization SymRegExp." << std::endl;
      Assert(false);
    }
  }
  return ret;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
