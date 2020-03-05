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
#include "theory/ext_theory.h"
#include "theory/strings/theory_strings.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/theory_model.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

RegExpSolver::RegExpSolver(TheoryStrings& p,
                           SolverState& s,
                           InferenceManager& im,
                           ExtfSolver& es,
                           context::Context* c,
                           context::UserContext* u)
    : d_parent(p),
      d_state(s),
      d_im(im),
      d_esolver(es),
      d_regexp_ucached(u),
      d_regexp_ccached(c),
      d_processed_memberships(c)
{
  d_emptyString = NodeManager::currentNM()->mkConst(::CVC4::String(""));
  std::vector<Node> nvec;
  d_emptyRegexp = NodeManager::currentNM()->mkNode(REGEXP_EMPTY, nvec);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

Node RegExpSolver::mkAnd(Node c1, Node c2)
{
  return NodeManager::currentNM()->mkNode(AND, c1, c2);
}

void RegExpSolver::checkMemberships()
{
  // add the memberships
  std::vector<Node> mems = d_esolver.getActive(STRING_IN_REGEXP);
  // maps representatives to regular expression memberships in that class
  std::map<Node, std::vector<Node> > assertedMems;
  const std::map<Node, ExtfInfoTmp>& einfo = d_esolver.getInfo();
  std::map<Node, ExtfInfoTmp>::const_iterator it;
  for (unsigned i = 0; i < mems.size(); i++)
  {
    Node n = mems[i];
    Assert(n.getKind() == STRING_IN_REGEXP);
    it = einfo.find(n);
    Assert(it != einfo.end());
    if (!it->second.d_const.isNull())
    {
      bool pol = it->second.d_const.getConst<bool>();
      Trace("strings-process-debug")
          << "  add membership : " << n << ", pol = " << pol << std::endl;
      Node r = d_state.getRepresentative(n[0]);
      assertedMems[r].push_back(pol ? n : n.negate());
    }
    else
    {
      Trace("strings-process-debug")
          << "  irrelevant (non-asserted) membership : " << n << std::endl;
    }
  }
  check(assertedMems);
}

void RegExpSolver::check(const std::map<Node, std::vector<Node> >& mems)
{
  bool addedLemma = false;
  bool changed = false;
  std::vector<Node> processed;
  std::vector<Node> cprocessed;

  Trace("regexp-process") << "Checking Memberships ... " << std::endl;
  for (const std::pair<const Node, std::vector<Node> >& mr : mems)
  {
    std::vector<Node> mems2 = mr.second;
    Trace("regexp-process")
        << "Memberships(" << mr.first << ") = " << mr.second << std::endl;
    if (!checkEqcInclusion(mems2))
    {
      // conflict discovered, return
      return;
    }
    if (!checkEqcIntersect(mems2))
    {
      // conflict discovered, return
      return;
    }
  }

  Trace("regexp-debug")
      << "... No Intersect Conflict in Memberships, addedLemma: " << addedLemma
      << std::endl;
  if (!addedLemma)
  {
    // get all memberships
    std::map<Node, Node> allMems;
    for (const std::pair<const Node, std::vector<Node> >& mr : mems)
    {
      for (const Node& m : mr.second)
      {
        bool polarity = m.getKind() != NOT;
        if (polarity || !options::stringIgnNegMembership())
        {
          allMems[m] = mr.first;
        }
      }
    }

    NodeManager* nm = NodeManager::currentNM();
    // representatives of strings that are the LHS of positive memberships that
    // we unfolded
    std::unordered_set<Node, NodeHashFunction> repUnfold;
    // check positive (e=0), then negative (e=1) memberships
    for (unsigned e = 0; e < 2; e++)
    {
      for (const std::pair<const Node, Node>& mp : allMems)
      {
        Node assertion = mp.first;
        Node rep = mp.second;
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
        Assert(rep == d_state.getRepresentative(x));
        // The following code takes normal forms into account for the purposes
        // of simplifying a regular expression membership x in R. For example,
        // if x = "A" in the current context, then we may be interested in
        // reasoning about ( x in R ) * { x -> "A" }. Say we update the
        // membership to nx in R', then:
        // - nfexp => ( x in R ) <=> nx in R'
        // - rnfexp => R = R'
        // We use these explanations below as assumptions on inferences when
        // appropriate. Notice that for inferring conflicts and tautologies,
        // we use the normal form of x always. This is because we always want to
        // discover conflicts/tautologies whenever possible.
        // For inferences based on regular expression unfolding, we do not use
        // the normal form of x. The reason is that it is better to unfold
        // regular expression memberships in a context-indepedent manner,
        // that is, not taking into account the current normal form of x, since
        // this ensures these lemmas are still relevant after backtracking.
        std::vector<Node> nfexp;
        std::vector<Node> rnfexp;
        // The normal form of x is stored in nx, while x is left unchanged.
        Node nx = x;
        if (!x.isConst())
        {
          nx = d_parent.getNormalString(x, nfexp);
        }
        // If r is not a constant regular expression, we update it based on
        // normal forms, which may concretize its variables.
        if (!d_regexp_opr.checkConstRegExp(r))
        {
          r = getNormalSymRegExp(r, rnfexp);
          nfexp.insert(nfexp.end(), rnfexp.begin(), rnfexp.end());
          changed = true;
        }
        Trace("strings-regexp-nf") << "Term " << atom << " is normalized to "
                                   << nx << " IN " << r << std::endl;
        if (nx != x || changed)
        {
          // We rewrite the membership nx IN r.
          Node tmp = Rewriter::rewrite(nm->mkNode(STRING_IN_REGEXP, nx, r));
          Trace("strings-regexp-nf") << "Simplifies to " << tmp << std::endl;
          if (tmp.isConst())
          {
            if (tmp.getConst<bool>() == polarity)
            {
              // it is satisfied in this SAT context
              d_regexp_ccached.insert(assertion);
              continue;
            }
            else
            {
              // we have a conflict
              std::vector<Node> exp_n;
              exp_n.push_back(assertion);
              Node conc = Node::null();
              d_im.sendInference(nfexp, exp_n, conc, "REGEXP NF Conflict");
              addedLemma = true;
              break;
            }
          }
        }
        if (e == 1 && repUnfold.find(rep) != repUnfold.end())
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
          Trace("strings-regexp")
              << "Unroll/simplify membership of atomic term " << rep
              << std::endl;
          // if so, do simple unrolling
          std::vector<Node> nvec;
          Trace("strings-regexp") << "Simplify on " << atom << std::endl;
          d_regexp_opr.simplify(atom, nvec, polarity);
          Trace("strings-regexp") << "...finished" << std::endl;
          // if simplifying successfully generated a lemma
          if (!nvec.empty())
          {
            std::vector<Node> exp_n;
            exp_n.push_back(assertion);
            Node conc = nvec.size() == 1 ? nvec[0] : nm->mkNode(AND, nvec);
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
              repUnfold.insert(rep);
            }
          }
          else
          {
            // otherwise we are incomplete
            d_parent.getOutputChannel().setIncomplete();
          }
        }
        if (d_state.isInConflict())
        {
          break;
        }
      }
    }
  }
  if (addedLemma)
  {
    if (!d_state.isInConflict())
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

bool RegExpSolver::checkEqcInclusion(std::vector<Node>& mems)
{
  std::unordered_set<Node, NodeHashFunction> remove;

  for (const Node& m1 : mems)
  {
    bool m1Neg = m1.getKind() == NOT;
    Node m1Lit = m1Neg ? m1[0] : m1;

    if (remove.find(m1) != remove.end())
    {
      // Skip memberships marked for removal
      continue;
    }

    for (const Node& m2 : mems)
    {
      if (m1 == m2)
      {
        continue;
      }

      bool m2Neg = m2.getKind() == NOT;
      Node m2Lit = m2Neg ? m2[0] : m2;

      // Both regular expression memberships have the same polarity
      if (m1Neg == m2Neg)
      {
        if (d_regexp_opr.regExpIncludes(m1Lit[1], m2Lit[1]))
        {
          if (m1Neg)
          {
            // ~str.in.re(x, R1) includes ~str.in.re(x, R2) --->
            //   mark ~str.in.re(x, R2) as reduced
            d_parent.getExtTheory()->markReduced(m2Lit);
            remove.insert(m2);
          }
          else
          {
            // str.in.re(x, R1) includes str.in.re(x, R2) --->
            //   mark str.in.re(x, R1) as reduced
            d_parent.getExtTheory()->markReduced(m1Lit);
            remove.insert(m1);

            // We don't need to process m1 anymore
            break;
          }
        }
      }
      else
      {
        Node pos = m1Neg ? m2Lit : m1Lit;
        Node neg = m1Neg ? m1Lit : m2Lit;
        if (d_regexp_opr.regExpIncludes(neg[1], pos[1]))
        {
          // We have a conflict because we have a case where str.in.re(x, R1)
          // and ~str.in.re(x, R2) but R2 includes R1, so there is no
          // possible value for x that satisfies both memberships.
          std::vector<Node> vec_nodes;
          vec_nodes.push_back(pos);
          vec_nodes.push_back(neg.negate());

          if (pos[0] != neg[0])
          {
            vec_nodes.push_back(pos[0].eqNode(neg[0]));
          }

          Node conc;
          d_im.sendInference(vec_nodes, conc, "Intersect inclusion", true);
          return false;
        }
      }
    }
  }

  mems.erase(std::remove_if(
                 mems.begin(),
                 mems.end(),
                 [&remove](Node& n) { return remove.find(n) != remove.end(); }),
             mems.end());

  return true;
}

bool RegExpSolver::checkEqcIntersect(const std::vector<Node>& mems)
{
  // do not compute intersections if the re intersection mode is none
  if (options::stringRegExpInterMode() == options::RegExpInterMode::NONE)
  {
    return true;
  }
  if (mems.empty())
  {
    // nothing to do
    return true;
  }
  // the initial regular expression membership and its constant type
  Node mi;
  RegExpConstType rcti = RE_C_UNKNOWN;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& m : mems)
  {
    if (m.getKind() != STRING_IN_REGEXP)
    {
      // do not do negative
      Assert(m.getKind() == NOT && m[0].getKind() == STRING_IN_REGEXP);
      continue;
    }
    RegExpConstType rct = d_regexp_opr.getRegExpConstType(m[1]);
    if (rct == RE_C_VARIABLE
        || (options::stringRegExpInterMode()
                == options::RegExpInterMode::CONSTANT
            && rct != RE_C_CONRETE_CONSTANT))
    {
      // cannot do intersection on RE with variables, or with re.allchar based
      // on option.
      continue;
    }
    if (options::stringRegExpInterMode()
        == options::RegExpInterMode::ONE_CONSTANT)
    {
      if (!mi.isNull() && rcti >= RE_C_CONSTANT && rct >= RE_C_CONSTANT)
      {
        // if both have re.allchar, do not do intersection if the
        // options::RegExpInterMode::ONE_CONSTANT option is set.
        continue;
      }
    }
    if (mi.isNull())
    {
      // first regular expression seen
      mi = m;
      rcti = rct;
      continue;
    }
    bool spflag = false;
    Node resR = d_regexp_opr.intersect(mi[1], m[1], spflag);
    // intersection should be computable
    Assert(!resR.isNull());
    Assert(!spflag);
    if (resR == d_emptyRegexp)
    {
      // conflict, explain
      std::vector<Node> vec_nodes;
      vec_nodes.push_back(mi);
      vec_nodes.push_back(m);
      if (mi[0] != m[0])
      {
        vec_nodes.push_back(mi[0].eqNode(m[0]));
      }
      Node conc;
      d_im.sendInference(vec_nodes, conc, "INTERSECT CONFLICT", true);
      // conflict, return
      return false;
    }
    // rewrite to ensure the equality checks below are precise
    Node mres = Rewriter::rewrite(nm->mkNode(STRING_IN_REGEXP, mi[0], resR));
    if (mres == mi)
    {
      // if R1 = intersect( R1, R2 ), then x in R1 ^ x in R2 is equivalent
      // to x in R1, hence x in R2 can be marked redundant.
      d_parent.getExtTheory()->markReduced(m);
    }
    else if (mres == m)
    {
      // same as above, opposite direction
      d_parent.getExtTheory()->markReduced(mi);
    }
    else
    {
      // new conclusion
      // (x in R ^ y in R2 ^ x = y) => (x in intersect(R1,R2))
      std::vector<Node> vec_nodes;
      vec_nodes.push_back(mi);
      vec_nodes.push_back(m);
      if (mi[0] != m[0])
      {
        vec_nodes.push_back(mi[0].eqNode(m[0]));
      }
      d_im.sendInference(vec_nodes, mres, "INTERSECT INFER", true);
      // both are reduced
      d_parent.getExtTheory()->markReduced(m);
      d_parent.getExtTheory()->markReduced(mi);
      // do not send more than one lemma for this class
      return true;
    }
  }
  return true;
}

bool RegExpSolver::checkPDerivative(
    Node x, Node r, Node atom, bool& addedLemma, std::vector<Node>& nf_exp)
{
  if (d_state.areEqual(x, d_emptyString))
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
        Assert(false)
            << "Impossible: RegExpSolver::deriveRegExp: const string in const "
               "regular expression.";
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
        Node left = utils::mkConcat(STRING_CONCAT, vec_nodes);
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
      Assert(!RegExpOpr::isRegExpKind(r.getKind()));
    }
  }
  return ret;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
