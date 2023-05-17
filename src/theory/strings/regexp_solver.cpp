/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "util/statistics_value.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
      d_regexp_opr(env, tr.getSkolemCache())
{
  d_emptyString = NodeManager::currentNM()->mkConst(cvc5::internal::String(""));
  d_emptyRegexp = NodeManager::currentNM()->mkNode(REGEXP_NONE);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

std::map<Node, std::vector<Node>> RegExpSolver::computeAssertions(Kind k) const
{
  std::map<Node, std::vector<Node>> assertions;
  // add the memberships
  std::vector<Node> xts = d_esolver.getActive(k);
  // maps representatives to regular expression memberships in that class
  for (const Node& n : xts)
  {
    Assert(n.getKind() == k);
    Node r = d_state.getRepresentative(n);
    if (r.isConst())
    {
      bool pol = r.getConst<bool>();
      Trace("strings-process-debug")
          << "  add predicate : " << n << ", pol = " << pol << std::endl;
      r = d_state.getRepresentative(n[0]);
      assertions[r].push_back(pol ? n : n.negate());
    }
    else
    {
      Trace("strings-process-debug")
          << "  irrelevant (non-asserted) predicate : " << n << std::endl;
    }
  }
  return assertions;
}

void RegExpSolver::computeAssertedMemberships()
{
  d_assertedMems = computeAssertions(STRING_IN_REGEXP);
}

void RegExpSolver::checkMemberships(Theory::Effort e)
{
  Trace("regexp-process") << "Checking Memberships, effort = " << e << " ... "
                          << std::endl;
  // compute the memberships
  computeAssertedMemberships();
  if (e == Theory::EFFORT_FULL)
  {
    // check for regular expression inclusion
    checkInclusions();
    if (d_state.isInConflict())
    {
      return;
    }
    // check for evaluations and inferences based on derivatives
    checkEvaluations();
    if (d_state.isInConflict())
    {
      return;
    }
  }
  checkUnfold(e);
}

void RegExpSolver::checkInclusions()
{
  // Check for conflict and chances to mark memberships inactive based on
  // regular expression and intersection.
  Trace("regexp-process") << "Checking inclusion/intersection ... "
                          << std::endl;
  for (const std::pair<const Node, std::vector<Node>>& mr : d_assertedMems)
  {
    // copy the vector because it is modified in the call below
    std::vector<Node> mems2 = mr.second;
    Trace("regexp-process")
        << "Memberships(" << mr.first << ") = " << mr.second << std::endl;
    if (options().strings.stringRegexpInclusion && !checkEqcInclusion(mems2))
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
  Trace("regexp-debug") << "... No Intersect Conflict in Memberships"
                        << std::endl;
}

void RegExpSolver::checkMembershipsEager()
{
  if (!options().strings.stringRegexpPosConcatEager)
  {
    // option not enabled
    return;
  }
  // eagerly reduce positive membership into re.++
  std::vector<Node> mems = d_esolver.getActive(STRING_IN_REGEXP);
  for (const Node& n : mems)
  {
    Assert(n.getKind() == STRING_IN_REGEXP);
    if (n[1].getKind() != REGEXP_CONCAT)
    {
      // not a membership into concatenation
      continue;
    }
    if (d_esolver.isReduced(n))
    {
      // already reduced
      continue;
    }
    Node r = d_state.getRepresentative(n);
    if (!r.isConst() || !r.getConst<bool>())
    {
      // not asserted true
      continue;
    }
    // unfold it
    doUnfold(n);
  }
}

bool RegExpSolver::shouldUnfold(Theory::Effort e, bool pol) const
{
  // Check positive, then negative memberships. If we are doing
  // model-based reductions, we process positive ones at FULL effort, and
  // negative ones at LAST_CALL effort.
  if (options().strings.stringModelBasedReduction)
  {
    if (pol)
    {
      return e == Theory::EFFORT_FULL;
    }
    return e == Theory::EFFORT_LAST_CALL;
  }
  // Otherwise we don't make the distinction
  return true;
}

void RegExpSolver::checkUnfold(Theory::Effort e)
{
  Trace("regexp-process") << "Checking unfold ... " << std::endl;
  // get all memberships
  std::map<Node, Node> allMems;
  for (const std::pair<const Node, std::vector<Node>>& mr : d_assertedMems)
  {
    for (const Node& m : mr.second)
    {
      allMems[m] = mr.first;
    }
  }
  // representatives of strings that are the LHS of positive memberships that
  // we unfolded
  std::unordered_set<Node> repUnfold;
  for (size_t eval = 0; eval < 2; eval++)
  {
    // skip if we should not unfold
    bool checkPol = (eval == 0);
    if (!shouldUnfold(e, checkPol))
    {
      continue;
    }
    for (const std::pair<const Node, Node>& mp : allMems)
    {
      Node assertion = mp.first;
      Node rep = mp.second;
      bool polarity = assertion.getKind() != NOT;
      if (polarity != checkPol)
      {
        continue;
      }
      // check regular expression membership
      Trace("regexp-debug") << "Check : " << assertion << " "
                            << (d_esolver.isReduced(assertion)) << std::endl;
      if (d_esolver.isReduced(assertion))
      {
        continue;
      }
      Node atom = polarity ? assertion : assertion[0];
      Trace("strings-regexp")
          << "We have regular expression assertion : " << assertion
          << std::endl;
      Assert(atom == rewrite(atom));
      if (e == Theory::EFFORT_LAST_CALL && !d_esolver.isActiveInModel(atom))
      {
        Trace("strings-regexp")
            << "...ignore since inactive in model" << std::endl;
        continue;
      }
      if (!checkPol && repUnfold.find(rep) != repUnfold.end())
      {
        // do not unfold negative memberships of strings that have new
        // positive unfoldings. For example:
        //   x in ("A")* ^ NOT x in ("B")*
        // We unfold x = "A" ++ x' only. The intution here is that positive
        // unfoldings lead to stronger constraints (equalities are stronger
        // than disequalities), and are easier to check.
        continue;
      }
      if (!polarity)
      {
        if (!options().strings.stringExp)
        {
          throw LogicException(
              "Strings Incomplete (due to Negative Membership) by default, "
              "try --strings-exp option.");
        }
      }
      // check if the term is atomic
      Trace("strings-regexp")
          << "Unroll/simplify membership of atomic term " << rep << std::endl;
      // if so, do simple unrolling
      if (doUnfold(assertion))
      {
        if (checkPol)
        {
          // Remember that we have unfolded a membership for x
          // notice that we only do this here, after we have definitely
          // added a lemma.
          repUnfold.insert(rep);
        }
      }
    }
    if (d_state.isInConflict())
    {
      break;
    }
  }
}

bool RegExpSolver::doUnfold(const Node& assertion)
{
  bool ret = false;
  bool polarity = assertion.getKind() != NOT;
  Node atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == STRING_IN_REGEXP);
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
    ret = d_im.sendInference(iexp, noExplain, conc, inf);
    d_esolver.markReduced(assertion);
  }
  else
  {
    // otherwise we are incomplete
    d_im.setModelUnsound(IncompleteId::STRINGS_REGEXP_NO_SIMPLIFY);
  }
  return ret;
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
        bool basisUnfolded = d_esolver.isReduced(m1Neg ? m1 : m2);
        if (!basisUnfolded)
        {
          // Both regular expression memberships have positive polarity
          if (d_regexp_opr.regExpIncludes(m1Lit[1], m2Lit[1]))
          {
            if (m1Neg)
            {
              // ~str.in.re(x, R1) includes ~str.in.re(x, R2) --->
              //   mark ~str.in.re(x, R2) as inactive
              d_im.markInactive(m2Lit,
                                ExtReducedId::STRINGS_REGEXP_INCLUDE_NEG);
              remove.insert(m2);
            }
            else
            {
              // str.in.re(x, R1) includes str.in.re(x, R2) --->
              //   mark str.in.re(x, R1) as inactive
              d_im.markInactive(m1Lit, ExtReducedId::STRINGS_REGEXP_INCLUDE);
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
            && rct != RE_C_CONCRETE_CONSTANT))
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
    if (resR.isNull())
    {
      // failed to compute intersection, e.g. if there was a complement
      continue;
    }
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
      d_im.markInactive(m, ExtReducedId::STRINGS_REGEXP_INTER_SUBSUME);
    }
    else if (mresr == m)
    {
      // same as above, opposite direction
      d_im.markInactive(mi, ExtReducedId::STRINGS_REGEXP_INTER_SUBSUME);
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
      // both are inactive
      d_im.markInactive(m, ExtReducedId::STRINGS_REGEXP_INTER);
      d_im.markInactive(mi, ExtReducedId::STRINGS_REGEXP_INTER);
      // do not send more than one lemma for this class
      return true;
    }
  }
  return true;
}

bool RegExpSolver::checkPDerivative(Node x,
                                    Node r,
                                    Node atom,
                                    std::vector<Node>& nf_exp)
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
        d_im.markInactive(atom, ExtReducedId::STRINGS_REGEXP_PDERIVATIVE);
        return false;
      }
      case 1:
      {
        d_im.markInactive(atom, ExtReducedId::STRINGS_REGEXP_PDERIVATIVE);
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
      d_im.markInactive(atom, ExtReducedId::STRINGS_REGEXP_PDERIVATIVE);
      return false;
    }
  }
  return true;
}

cvc5::internal::String RegExpSolver::getHeadConst(Node x)
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
  cvc5::internal::String s = getHeadConst(x);
  // only allow RE_DERIVE for concrete constant regular expressions
  if (!s.empty()
      && d_regexp_opr.getRegExpConstType(r) == RE_C_CONCRETE_CONSTANT)
  {
    Node conc = Node::null();
    Node dc = r;
    bool flag = true;
    for (unsigned i = 0; i < s.size(); ++i)
    {
      cvc5::internal::String c = s.substr(i, 1);
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

void RegExpSolver::checkEvaluations()
{
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, std::vector<Node>>& mr : d_assertedMems)
  {
    Node rep = mr.first;
    for (const Node& assertion : mr.second)
    {
      bool polarity = assertion.getKind() != NOT;
      Node atom = polarity ? assertion : assertion[0];
      Trace("strings-regexp")
          << "We have regular expression assertion : " << assertion
          << std::endl;
      Assert(atom == rewrite(atom));
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
      if (!d_regexp_opr.checkConstRegExp(r))
      {
        r = getNormalSymRegExp(r, rnfexp);
        nfexp.insert(nfexp.end(), rnfexp.begin(), rnfexp.end());
        Trace("strings-regexp-nf") << "Term " << atom << " is normalized to "
                                   << nx << " IN " << r << std::endl;

        // We rewrite the membership nx IN r.
        Node tmp = rewrite(nm->mkNode(STRING_IN_REGEXP, nx, r));
        Trace("strings-regexp-nf") << "Simplifies to " << tmp << std::endl;
        if (tmp.isConst())
        {
          if (tmp.getConst<bool>() == polarity)
          {
            // it is satisfied in this SAT context
            d_im.markInactive(atom, ExtReducedId::STRINGS_REGEXP_RE_SYM_NF);
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
            break;
          }
        }
      }
      if (polarity)
      {
        checkPDerivative(x, r, atom, rnfexp);
      }
    }
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
