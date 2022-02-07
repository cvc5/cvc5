/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the regular expression solver for the theory of strings.
 */

#include "theory/strings/regexp_solver.h"

#include <cmath>

#include "options/strings_options.h"
#include "smt/logic_exception.h"
#include "theory/ext_theory.h"
#include "theory/strings/term_registry.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/theory_model.h"
#include "util/statistics_value.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace strings {

RegExpSolver::RegExpSolver(Env& env,
                           SolverState& s,
                           InferenceManager& im,
                           TermRegistry& tr,
                           CoreSolver& cs,
                           ExtfSolver& es,
                           SequencesStatistics& stats)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_csolver(cs),
      d_esolver(es),
      d_statistics(stats),
      d_regexp_ucached(userContext()),
      d_regexp_ccached(context()),
      d_processed_memberships(context()),
      d_regexp_opr(env, tr.getSkolemCache())
{
  d_emptyString = NodeManager::currentNM()->mkConst(::cvc5::String(""));
  d_emptyRegexp = NodeManager::currentNM()->mkNode(REGEXP_NONE);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

Node RegExpSolver::mkAnd(Node c1, Node c2)
{
  return NodeManager::currentNM()->mkNode(AND, c1, c2);
}

void RegExpSolver::checkMemberships(int effort)
{
  Trace("regexp-process") << "Checking Memberships, effort = " << effort
                          << " ... " << std::endl;
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
  if (effort == 0)
  {
    // First check for conflict. We do this only if effort is 0, otherwise
    // we have already run these checks in this SAT context.
    if (checkInclInter(assertedMems))
    {
      return;
    }
  }
  checkUnfold(assertedMems, effort);
}

bool RegExpSolver::checkInclInter(
    const std::map<Node, std::vector<Node> >& mems)
{
  Trace("regexp-process") << "Checking inclusion/intersection ... "
                          << std::endl;
  for (const std::pair<const Node, std::vector<Node> >& mr : mems)
  {
    // copy the vector because it is modified in the call below
    std::vector<Node> mems2 = mr.second;
    Trace("regexp-process")
        << "Memberships(" << mr.first << ") = " << mr.second << std::endl;
    if (options().strings.stringRegexpInclusion && !checkEqcInclusion(mems2))
    {
      // conflict discovered, return
      return true;
    }
    if (!checkEqcIntersect(mems2))
    {
      // conflict discovered, return
      return true;
    }
  }
  Trace("regexp-debug") << "... No Intersect Conflict in Memberships"
                        << std::endl;
  return false;
}

void RegExpSolver::checkUnfold(const std::map<Node, std::vector<Node> >& mems,
                               int effort)
{
  Trace("regexp-process") << "Checking unfold ... " << std::endl;
  bool addedLemma = false;
  std::vector<Node> processed;

  // get all memberships
  std::map<Node, Node> allMems;
  for (const std::pair<const Node, std::vector<Node> >& mr : mems)
  {
    for (const Node& m : mr.second)
    {
      allMems[m] = mr.first;
    }
  }

  NodeManager* nm = NodeManager::currentNM();
  // representatives of strings that are the LHS of positive memberships that
  // we unfolded
  std::unordered_set<Node> repUnfold;
  // Check positive (e=0), then negative (e=1) memberships. If we are doing
  // model-based reductions, we process positive ones at effort=0, and negative
  // ones at effort=3.
  bool mbr = options().strings.stringModelBasedReduction;
  size_t startE = mbr ? (effort > 0 ? 1 : 0) : 0;
  size_t endE = mbr ? (effort > 0 ? 2 : 1) : 2;
  for (size_t e = startE; e < endE; e++)
  {
    for (const std::pair<const Node, Node>& mp : allMems)
    {
      Node assertion = mp.first;
      Node rep = mp.second;
      bool polarity = assertion.getKind() != NOT;
      if (polarity != (e == 0))
      {
        continue;
      }
      // check regular expression membership
      Trace("regexp-debug")
          << "Check : " << assertion << " "
          << (d_regexp_ucached.find(assertion) == d_regexp_ucached.end()) << " "
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
      Assert(atom == rewrite(atom));
      if (effort > 0 && !d_esolver.isActiveInModel(atom))
      {
        Trace("strings-regexp")
            << "...ignore since inactive in model" << std::endl;
        continue;
      }
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
        nx = d_csolver.getNormalString(x, nfexp);
      }
      // If r is not a constant regular expression, we update it based on
      // normal forms, which may concretize its variables.
      bool changed = false;
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
        Node tmp = rewrite(nm->mkNode(STRING_IN_REGEXP, nx, r));
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
            std::vector<Node> iexp = nfexp;
            std::vector<Node> noExplain;
            iexp.push_back(assertion);
            noExplain.push_back(assertion);
            Node conc = Node::null();
            d_im.sendInference(
                iexp, noExplain, conc, InferenceId::STRINGS_RE_NF_CONFLICT);
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
      bool doSimplify = true;
      if (polarity)
      {
        doSimplify = checkPDerivative(x, r, atom, addedLemma, rnfexp);
      }
      else
      {
        if (!options().strings.stringExp)
        {
          throw LogicException(
              "Strings Incomplete (due to Negative Membership) by default, "
              "try --strings-exp option.");
        }
      }
      if (doSimplify)
      {
        // check if the term is atomic
        Trace("strings-regexp")
            << "Unroll/simplify membership of atomic term " << rep << std::endl;
        // if so, do simple unrolling
        Trace("strings-regexp") << "Simplify on " << atom << std::endl;
        Node conc = d_regexp_opr.simplify(atom, polarity);
        Trace("strings-regexp") << "...finished, got " << conc << std::endl;
        // if simplifying successfully generated a lemma
        if (!conc.isNull())
        {
          std::vector<Node> iexp;
          std::vector<Node> noExplain;
          iexp.push_back(assertion);
          noExplain.push_back(assertion);
          Assert(atom.getKind() == STRING_IN_REGEXP);
          if (polarity)
          {
            d_statistics.d_regexpUnfoldingsPos << atom[1].getKind();
          }
          else
          {
            d_statistics.d_regexpUnfoldingsNeg << atom[1].getKind();
          }
          InferenceId inf = polarity ? InferenceId::STRINGS_RE_UNFOLD_POS
                                     : InferenceId::STRINGS_RE_UNFOLD_NEG;
          // in very rare cases, we may find out that the unfolding lemma
          // for a membership is equivalent to true, in spite of the RE
          // not being rewritten to true.
          if (d_im.sendInference(iexp, noExplain, conc, inf))
          {
            addedLemma = true;
            if (e == 0)
            {
              // Remember that we have unfolded a membership for x
              // notice that we only do this here, after we have definitely
              // added a lemma.
              repUnfold.insert(rep);
            }
          }
          processed.push_back(assertion);
        }
        else
        {
          // otherwise we are incomplete
          d_im.setIncomplete(IncompleteId::STRINGS_REGEXP_NO_SIMPLIFY);
        }
      }
      if (d_state.isInConflict())
      {
        break;
      }
    }
  }

  if (addedLemma)
  {
    if (!d_state.isInConflict())
    {
      for (const Node& p : processed)
      {
        Trace("strings-regexp")
            << "...add " << p << " to u-cache." << std::endl;
        d_regexp_ucached.insert(p);
      }
    }
  }
}

bool RegExpSolver::checkEqcInclusion(std::vector<Node>& mems)
{
  std::unordered_set<Node> remove;

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

      if (m1Neg == m2Neg)
      {
        // Check whether the RE in membership m1 contains the one in m2, if
        // so then m1 can be marked reduced if positive polarity, m2 if
        // negative polarity.
        // Notice that we do not do this if the non-reduced membership has
        // already been unfolded, since memberships may reduce to other
        // memberships that are included in the original, thus making the
        // justification for the reduction cyclic.  For example, to reduce:
        //  (not (str.in_re x (re.++ (re.* R1) R2)))
        // We may rely on justifying this by the fact that (writing x[i:j] for
        // substring) either:
        //  (not (str.in_re x[:0] (re.* R1)))
        //  (not (str.in_re x[0:] R2))
        // The first is trivially satisfied, the second is equivalent to
        //  (not (str.in_re x R2))
        // where R2 is included in (re.++ (re.* R1) R2)). However, we cannot
        // mark the latter as reduced.
        bool basisUnfolded =
            d_regexp_ucached.find(m1Neg ? m1 : m2) != d_regexp_ucached.end();
        if (!basisUnfolded)
        {
          // Both regular expression memberships have positive polarity
          if (d_regexp_opr.regExpIncludes(m1Lit[1], m2Lit[1]))
          {
            if (m1Neg)
            {
              // ~str.in.re(x, R1) includes ~str.in.re(x, R2) --->
              //   mark ~str.in.re(x, R2) as reduced
              d_im.markReduced(m2Lit, ExtReducedId::STRINGS_REGEXP_INCLUDE_NEG);
              remove.insert(m2);
            }
            else
            {
              // str.in.re(x, R1) includes str.in.re(x, R2) --->
              //   mark str.in.re(x, R1) as reduced
              d_im.markReduced(m1Lit, ExtReducedId::STRINGS_REGEXP_INCLUDE);
              remove.insert(m1);

              // We don't need to process m1 anymore
              break;
            }
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
          d_im.sendInference(
              vec_nodes, conc, InferenceId::STRINGS_RE_INTER_INCLUDE, false, true);
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
  if (options().strings.stringRegExpInterMode == options::RegExpInterMode::NONE)
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
        || (options().strings.stringRegExpInterMode
                == options::RegExpInterMode::CONSTANT
            && rct != RE_C_CONRETE_CONSTANT))
    {
      // cannot do intersection on RE with variables, or with re.allchar based
      // on option.
      continue;
    }
    if (options().strings.stringRegExpInterMode
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
    Node resR = d_regexp_opr.intersect(mi[1], m[1]);
    // intersection should be computable
    Assert(!resR.isNull());
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
      d_im.sendInference(
          vec_nodes, conc, InferenceId::STRINGS_RE_INTER_CONF, false, true);
      // conflict, return
      return false;
    }
    // rewrite to ensure the equality checks below are precise
    Node mres = nm->mkNode(STRING_IN_REGEXP, mi[0], resR);
    Node mresr = rewrite(mres);
    if (mresr == mi)
    {
      // if R1 = intersect( R1, R2 ), then x in R1 ^ x in R2 is equivalent
      // to x in R1, hence x in R2 can be marked redundant.
      d_im.markReduced(m, ExtReducedId::STRINGS_REGEXP_INTER_SUBSUME);
    }
    else if (mresr == m)
    {
      // same as above, opposite direction
      d_im.markReduced(mi, ExtReducedId::STRINGS_REGEXP_INTER_SUBSUME);
    }
    else
    {
      // new conclusion
      // (x in R1 ^ y in R2 ^ x = y) => (x in intersect(R1,R2))
      std::vector<Node> vec_nodes;
      vec_nodes.push_back(mi);
      vec_nodes.push_back(m);
      if (mi[0] != m[0])
      {
        vec_nodes.push_back(mi[0].eqNode(m[0]));
      }
      d_im.sendInference(
          vec_nodes, mres, InferenceId::STRINGS_RE_INTER_INFER, false, true);
      // both are reduced
      d_im.markReduced(m, ExtReducedId::STRINGS_REGEXP_INTER);
      d_im.markReduced(mi, ExtReducedId::STRINGS_REGEXP_INTER);
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
        std::vector<Node> noExplain;
        noExplain.push_back(atom);
        noExplain.push_back(x.eqNode(d_emptyString));
        std::vector<Node> iexp = nf_exp;
        iexp.insert(iexp.end(), noExplain.begin(), noExplain.end());
        d_im.sendInference(iexp, noExplain, exp, InferenceId::STRINGS_RE_DELTA);
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
        std::vector<Node> noExplain;
        noExplain.push_back(atom);
        if (x != d_emptyString)
        {
          noExplain.push_back(x.eqNode(d_emptyString));
        }
        std::vector<Node> iexp = nf_exp;
        iexp.insert(iexp.end(), noExplain.begin(), noExplain.end());
        d_im.sendInference(iexp, noExplain, d_false, InferenceId::STRINGS_RE_DELTA_CONF);
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

cvc5::String RegExpSolver::getHeadConst(Node x)
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
  cvc5::String s = getHeadConst(x);
  // only allow RE_DERIVE for concrete constant regular expressions
  if (!s.empty() && d_regexp_opr.getRegExpConstType(r) == RE_C_CONRETE_CONSTANT)
  {
    Node conc = Node::null();
    Node dc = r;
    bool flag = true;
    for (unsigned i = 0; i < s.size(); ++i)
    {
      cvc5::String c = s.substr(i, 1);
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
        Node left = utils::mkConcat(vec_nodes, x.getType());
        left = rewrite(left);
        conc = NodeManager::currentNM()->mkNode(STRING_IN_REGEXP, left, dc);
      }
    }
    std::vector<Node> iexp = ant;
    std::vector<Node> noExplain;
    noExplain.push_back(atom);
    iexp.push_back(atom);
    d_im.sendInference(iexp, noExplain, conc, InferenceId::STRINGS_RE_DERIVE);
    return true;
  }
  return false;
}

Node RegExpSolver::getNormalSymRegExp(Node r, std::vector<Node>& nf_exp)
{
  Node ret = r;
  switch (r.getKind())
  {
    case REGEXP_NONE:
    case REGEXP_ALLCHAR:
    case REGEXP_RANGE: break;
    case STRING_TO_REGEXP:
    {
      if (!r[0].isConst())
      {
        Node tmp = d_csolver.getNormalString(r[0], nf_exp);
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
    case REGEXP_COMPLEMENT:
    {
      std::vector<Node> vec_nodes;
      for (const Node& cr : r)
      {
        vec_nodes.push_back(getNormalSymRegExp(cr, nf_exp));
      }
      ret = rewrite(NodeManager::currentNM()->mkNode(r.getKind(), vec_nodes));
      break;
    }
    default:
    {
      Trace("strings-error") << "Unsupported term: " << r
                             << " in normalization SymRegExp." << std::endl;
      Assert(!utils::isRegExpKind(r.getKind()));
    }
  }
  return ret;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5
