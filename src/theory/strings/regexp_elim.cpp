/*********************                                                        */
/*! \file regexp_elim.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniques for eliminating regular expressions
 **
 **/

#include "theory/strings/regexp_elim.h"

#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/theory_strings_utils.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

RegExpElimination::RegExpElimination()
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
  d_regExpType = NodeManager::currentNM()->regExpType();
}

Node RegExpElimination::eliminate(Node atom)
{
  Assert(atom.getKind() == STRING_IN_REGEXP);
  if (atom[1].getKind() == REGEXP_CONCAT)
  {
    return eliminateConcat(atom);
  }
  else if (atom[1].getKind() == REGEXP_STAR)
  {
    return eliminateStar(atom);
  }
  return Node::null();
}

Node RegExpElimination::eliminateConcat(Node atom)
{
  NodeManager* nm = NodeManager::currentNM();
  Node x = atom[0];
  Node lenx = nm->mkNode(STRING_LENGTH, x);
  Node re = atom[1];
  std::vector<Node> children;
  utils::getConcat(re, children);

  // If it can be reduced to memberships in fixed length regular expressions.
  // This includes concatenations where at most one child is of the form
  // (re.* re.allchar), which we abbreviate _* below, and all other children
  // have a fixed length.
  // The intuition why this is a "non-aggressive" rewrite is that membership
  // into fixed length regular expressions are easy to handle.
  bool hasFixedLength = true;
  // the index of _* in re
  unsigned pivotIndex = 0;
  bool hasPivotIndex = false;
  std::vector<Node> childLengths;
  std::vector<Node> childLengthsPostPivot;
  for (unsigned i = 0, size = children.size(); i < size; i++)
  {
    Node c = children[i];
    Node fl = RegExpEntail::getFixedLengthForRegexp(c);
    if (fl.isNull())
    {
      if (!hasPivotIndex && c.getKind() == REGEXP_STAR
          && c[0].getKind() == REGEXP_SIGMA)
      {
        hasPivotIndex = true;
        pivotIndex = i;
        // set to zero for the sum below
        fl = d_zero;
      }
      else
      {
        hasFixedLength = false;
        break;
      }
    }
    childLengths.push_back(fl);
    if (hasPivotIndex)
    {
      childLengthsPostPivot.push_back(fl);
    }
  }
  if (hasFixedLength)
  {
    Assert(re.getNumChildren() == children.size());
    Node sum = nm->mkNode(PLUS, childLengths);
    std::vector<Node> conc;
    conc.push_back(nm->mkNode(hasPivotIndex ? GEQ : EQUAL, lenx, sum));
    Node currEnd = d_zero;
    for (unsigned i = 0, size = childLengths.size(); i < size; i++)
    {
      if (hasPivotIndex && i == pivotIndex)
      {
        Node ppSum = childLengthsPostPivot.size() == 1
                         ? childLengthsPostPivot[0]
                         : nm->mkNode(PLUS, childLengthsPostPivot);
        currEnd = nm->mkNode(MINUS, lenx, ppSum);
      }
      else
      {
        Node curr = nm->mkNode(STRING_SUBSTR, x, currEnd, childLengths[i]);
        // We do not need to include memberships of the form
        //   (str.substr x n 1) in re.allchar
        // since we know that by construction, n < len( x ).
        if (re[i].getKind() != REGEXP_SIGMA)
        {
          Node currMem = nm->mkNode(STRING_IN_REGEXP, curr, re[i]);
          conc.push_back(currMem);
        }
        currEnd = nm->mkNode(PLUS, currEnd, childLengths[i]);
        currEnd = Rewriter::rewrite(currEnd);
      }
    }
    Node res = nm->mkNode(AND, conc);
    // For example:
    //   x in re.++(re.union(re.range("A", "J"), re.range("N", "Z")), "AB") -->
    //   len( x ) = 3 ^
    //   substr(x,0,1) in re.union(re.range("A", "J"), re.range("N", "Z")) ^
    //   substr(x,1,2) in "AB"
    // An example with a pivot index:
    //   x in re.++( "AB" ++ _* ++ "C" ) -->
    //   len( x ) >= 3 ^
    //   substr( x, 0, 2 ) in "AB" ^
    //   substr( x, len( x ) - 1, 1 ) in "C"
    return returnElim(atom, res, "concat-fixed-len");
  }

  // memberships of the form x in re.++ * s1 * ... * sn *, where * are
  // any number of repetitions (exact or indefinite) of re.allchar.
  Trace("re-elim-debug") << "Try re concat with gaps " << atom << std::endl;
  bool onlySigmasAndConsts = true;
  std::vector<Node> sep_children;
  std::vector<unsigned> gap_minsize;
  std::vector<bool> gap_exact;
  // the first gap is initially strict zero
  gap_minsize.push_back(0);
  gap_exact.push_back(true);
  for (const Node& c : children)
  {
    Trace("re-elim-debug") << "  " << c << std::endl;
    onlySigmasAndConsts = false;
    if (c.getKind() == STRING_TO_REGEXP)
    {
      onlySigmasAndConsts = true;
      sep_children.push_back(c[0]);
      // the next gap is initially strict zero
      gap_minsize.push_back(0);
      gap_exact.push_back(true);
    }
    else if (c.getKind() == REGEXP_STAR && c[0].getKind() == REGEXP_SIGMA)
    {
      // found a gap of any size
      onlySigmasAndConsts = true;
      gap_exact[gap_exact.size() - 1] = false;
    }
    else if (c.getKind() == REGEXP_SIGMA)
    {
      // add one to the minimum size of the gap
      onlySigmasAndConsts = true;
      gap_minsize[gap_minsize.size() - 1]++;
    }
    if (!onlySigmasAndConsts)
    {
      Trace("re-elim-debug") << "...cannot handle " << c << std::endl;
      break;
    }
  }
  // we should always rewrite concatenations that are purely re.allchar
  // and re.*( re.allchar ).
  Assert(!onlySigmasAndConsts || !sep_children.empty());
  if (onlySigmasAndConsts && !sep_children.empty())
  {
    bool canProcess = true;
    std::vector<Node> conj;
    // The following constructs a set of constraints that encodes that a
    // set of string terms are found, in order, in string x.
    // prev_end stores the current (symbolic) index in x that we are
    // searching.
    Node prev_end = d_zero;
    // the symbolic index we start searching, for each child in sep_children.
    std::vector<Node> prev_ends;
    unsigned gap_minsize_end = gap_minsize.back();
    bool gap_exact_end = gap_exact.back();
    std::vector<Node> non_greedy_find_vars;
    for (unsigned i = 0, size = sep_children.size(); i < size; i++)
    {
      if (gap_minsize[i] > 0)
      {
        // the gap to this child is at least gap_minsize[i]
        prev_end =
            nm->mkNode(PLUS, prev_end, nm->mkConst(Rational(gap_minsize[i])));
      }
      prev_ends.push_back(prev_end);
      Node sc = sep_children[i];
      Node lensc = nm->mkNode(STRING_LENGTH, sc);
      if (gap_exact[i])
      {
        // if the gap is exact, it is a substring constraint
        Node curr = prev_end;
        Node ss = nm->mkNode(STRING_SUBSTR, x, curr, lensc);
        conj.push_back(ss.eqNode(sc));
        prev_end = nm->mkNode(PLUS, curr, lensc);
      }
      else
      {
        // otherwise, we can use indexof to represent some next occurrence
        if (gap_exact[i + 1] && i + 1 != size)
        {
          if (!options::regExpElimAgg())
          {
            canProcess = false;
            break;
          }
          // if the gap after this one is strict, we need a non-greedy find
          // thus, we add a symbolic constant
          Node k = nm->mkBoundVar(nm->integerType());
          non_greedy_find_vars.push_back(k);
          prev_end = nm->mkNode(PLUS, prev_end, k);
        }
        Node curr = nm->mkNode(STRING_STRIDOF, x, sc, prev_end);
        Node idofFind = curr.eqNode(d_neg_one).negate();
        conj.push_back(idofFind);
        prev_end = nm->mkNode(PLUS, curr, lensc);
      }
    }

    if (canProcess)
    {
      // since sep_children is non-empty, conj is non-empty
      Assert(!conj.empty());
      // Process the last gap, if necessary.
      // Notice that if the last gap is not exact and its minsize is zero,
      // then the last indexof/substr constraint entails the following
      // constraint, so it is not necessary to add.
      // Below, we may write "A" for (str.to.re "A") and _ for re.allchar:
      Node cEnd = nm->mkConst(Rational(gap_minsize_end));
      if (gap_exact_end)
      {
        Assert(!sep_children.empty());
        // if it is strict, it corresponds to a substr case.
        // For example:
        //     x in (re.++ "A" (re.* _) "B" _ _) --->
        //        ... ^ "B" = substr( x, len( x ) - 3, 1 )  ^ ...
        Node sc = sep_children.back();
        Node lenSc = nm->mkNode(STRING_LENGTH, sc);
        Node loc = nm->mkNode(MINUS, lenx, nm->mkNode(PLUS, lenSc, cEnd));
        Node scc = sc.eqNode(nm->mkNode(STRING_SUBSTR, x, loc, lenSc));
        // We also must ensure that we fit. This constraint is necessary in
        // addition to the constraint above. Take this example:
        //     x in (re.++ "A" _ (re.* _) "B" _) --->
        //       substr( x, 0, 1 ) = "A" ^             // find "A"
        //       indexof( x, "B", 2 ) != -1 ^          // find "B" >=1 after "A"
        //       substr( x, len(x)-2, 1 ) = "B" ^      // "B" is at end - 2.
        //       indexof( x, "B", 2 ) <= len( x ) - 2
        // The last constaint ensures that the second and third constraints
        // may refer to the same "B". If it were not for the last constraint, it
        // would have been the case than "ABB" would be a model for x, where
        // the second constraint refers to the third position, and the third
        // constraint refers to the second position.
        //
        // With respect to the above example, the following is an optimization.
        // For that example, we instead produce:
        //     x in (re.++ "A" _ (re.* _) "B" _) --->
        //       substr( x, 0, 1 ) = "A" ^          // find "A"
        //       substr( x, len(x)-2, 1 ) = "B" ^   // "B" is at end - 2
        //       2 <= len( x ) - 2
        // The intuition is that above, there are two constraints that insist
        // that "B" is found, whereas we only need one. The last constraint
        // above says that the "B" we find at end-2 can be found >=1 after
        // the "A".
        conj.pop_back();
        Node fit = nm->mkNode(gap_exact[sep_children.size() - 1] ? EQUAL : LEQ,
                              prev_ends.back(),
                              loc);

        conj.push_back(scc);
        conj.push_back(fit);
      }
      else if (gap_minsize_end > 0)
      {
        // if it is non-strict, we are in a "greedy find" situtation where
        // we just need to ensure that the next occurrence fits.
        // For example:
        //     x in (re.++ "A" (re.* _) "B" _ _ (re.* _)) --->
        //        ... ^ indexof( x, "B", 1 ) + 2 <= len( x )
        Node fit = nm->mkNode(LEQ, nm->mkNode(PLUS, prev_end, cEnd), lenx);
        conj.push_back(fit);
      }
      Node res = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      // process the non-greedy find variables
      if (!non_greedy_find_vars.empty())
      {
        std::vector<Node> children2;
        for (const Node& v : non_greedy_find_vars)
        {
          Node bound = nm->mkNode(
              AND, nm->mkNode(LEQ, d_zero, v), nm->mkNode(LT, v, lenx));
          children2.push_back(bound);
        }
        children2.push_back(res);
        Node body = nm->mkNode(AND, children2);
        Node bvl = nm->mkNode(BOUND_VAR_LIST, non_greedy_find_vars);
        res = nm->mkNode(EXISTS, bvl, body);
      }
      // Examples of this elimination:
      //   x in (re.++ "A" (re.* _) "B" (re.* _)) --->
      //     substr(x,0,1)="A" ^ indexof(x,"B",1)!=-1
      //   x in (re.++ (re.* _) "A" _ _ _ (re.* _) "B" _ _ (re.* _)) --->
      //     indexof(x,"A",0)!=-1 ^
      //     indexof( x, "B", indexof( x, "A", 0 ) + 1 + 3 ) != -1 ^
      //     indexof( x, "B", indexof( x, "A", 0 ) + 1 + 3 )+1+2 <= len(x)

      // An example of a non-greedy find:
      //   x in re.++( re.*( _ ), "A", _, "B", re.*( _ ) ) --->
      //     exists k. 0 <= k < len( x ) ^
      //               indexof( x, "A", k ) != -1 ^
      //               substr( x, indexof( x, "A", k )+2, 1 ) = "B"
      return returnElim(atom, res, "concat-with-gaps");
    }
  }

  if (!options::regExpElimAgg())
  {
    return Node::null();
  }
  // only aggressive rewrites below here

  // if the first or last child is constant string, we can split the membership
  // into a conjunction of two memberships.
  Node sStartIndex = d_zero;
  Node sLength = lenx;
  std::vector<Node> sConstraints;
  std::vector<Node> rexpElimChildren;
  unsigned nchildren = children.size();
  Assert(nchildren > 1);
  for (unsigned r = 0; r < 2; r++)
  {
    unsigned index = r == 0 ? 0 : nchildren - 1;
    Node c = children[index];
    if (c.getKind() == STRING_TO_REGEXP)
    {
      Assert(children[index + (r == 0 ? 1 : -1)].getKind() != STRING_TO_REGEXP);
      Node s = c[0];
      Node lens = nm->mkNode(STRING_LENGTH, s);
      Node sss = r == 0 ? d_zero : nm->mkNode(MINUS, lenx, lens);
      Node ss = nm->mkNode(STRING_SUBSTR, x, sss, lens);
      sConstraints.push_back(ss.eqNode(s));
      if (r == 0)
      {
        sStartIndex = lens;
      }
      sLength = nm->mkNode(MINUS, sLength, lens);
    }
    if (r == 1 && !sConstraints.empty())
    {
      // add the middle children
      for (unsigned i = 1; i < (nchildren - 1); i++)
      {
        rexpElimChildren.push_back(children[i]);
      }
    }
    if (c.getKind() != STRING_TO_REGEXP)
    {
      rexpElimChildren.push_back(c);
    }
  }
  if (!sConstraints.empty())
  {
    Assert(rexpElimChildren.size() + sConstraints.size() == nchildren);
    Node ss = nm->mkNode(STRING_SUBSTR, x, sStartIndex, sLength);
    Assert(!rexpElimChildren.empty());
    Node regElim = utils::mkConcat(rexpElimChildren, d_regExpType);
    sConstraints.push_back(nm->mkNode(STRING_IN_REGEXP, ss, regElim));
    Node ret = nm->mkNode(AND, sConstraints);
    // e.g.
    // x in re.++( "A", R ) ---> substr(x,0,1)="A" ^ substr(x,1,len(x)-1) in R
    return returnElim(atom, ret, "concat-splice");
  }
  Assert(nchildren > 1);
  for (unsigned i = 0; i < nchildren; i++)
  {
    if (children[i].getKind() == STRING_TO_REGEXP)
    {
      Node s = children[i][0];
      Node lens = nm->mkNode(STRING_LENGTH, s);
      // there exists an index in this string such that the substring is this
      Node k;
      std::vector<Node> echildren;
      if (i == 0)
      {
        k = d_zero;
      }
      else if (i + 1 == nchildren)
      {
        k = nm->mkNode(MINUS, lenx, lens);
      }
      else
      {
        k = nm->mkBoundVar(nm->integerType());
        Node bound =
            nm->mkNode(AND,
                       nm->mkNode(LEQ, d_zero, k),
                       nm->mkNode(LEQ, k, nm->mkNode(MINUS, lenx, lens)));
        echildren.push_back(bound);
      }
      Node substrEq = nm->mkNode(STRING_SUBSTR, x, k, lens).eqNode(s);
      echildren.push_back(substrEq);
      if (i > 0)
      {
        std::vector<Node> rprefix;
        rprefix.insert(rprefix.end(), children.begin(), children.begin() + i);
        Node rpn = utils::mkConcat(rprefix, d_regExpType);
        Node substrPrefix = nm->mkNode(
            STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, x, d_zero, k), rpn);
        echildren.push_back(substrPrefix);
      }
      if (i + 1 < nchildren)
      {
        std::vector<Node> rsuffix;
        rsuffix.insert(rsuffix.end(), children.begin() + i + 1, children.end());
        Node rps = utils::mkConcat(rsuffix, d_regExpType);
        Node ks = nm->mkNode(PLUS, k, lens);
        Node substrSuffix = nm->mkNode(
            STRING_IN_REGEXP,
            nm->mkNode(STRING_SUBSTR, x, ks, nm->mkNode(MINUS, lenx, ks)),
            rps);
        echildren.push_back(substrSuffix);
      }
      Node body = nm->mkNode(AND, echildren);
      if (k.getKind() == BOUND_VARIABLE)
      {
        Node bvl = nm->mkNode(BOUND_VAR_LIST, k);
        body = nm->mkNode(EXISTS, bvl, body);
      }
      // e.g. x in re.++( R1, "AB", R2 ) --->
      //  exists k.
      //    0 <= k <= (len(x)-2) ^
      //    substr( x, k, 2 ) = "AB" ^
      //    substr( x, 0, k ) in R1 ^
      //    substr( x, k+2, len(x)-(k+2) ) in R2
      return returnElim(atom, body, "concat-find");
    }
  }
  return Node::null();
}

Node RegExpElimination::eliminateStar(Node atom)
{
  if (!options::regExpElimAgg())
  {
    return Node::null();
  }
  // only aggressive rewrites below here

  NodeManager* nm = NodeManager::currentNM();
  Node x = atom[0];
  Node lenx = nm->mkNode(STRING_LENGTH, x);
  Node re = atom[1];
  // for regular expression star,
  // if the period is a fixed constant, we can turn it into a bounded
  // quantifier
  std::vector<Node> disj;
  if (re[0].getKind() == REGEXP_UNION)
  {
    for (const Node& r : re[0])
    {
      disj.push_back(r);
    }
  }
  else
  {
    disj.push_back(re[0]);
  }
  bool lenOnePeriod = true;
  std::vector<Node> char_constraints;
  Node index = nm->mkBoundVar(nm->integerType());
  Node substr_ch = nm->mkNode(STRING_SUBSTR, x, index, d_one);
  substr_ch = Rewriter::rewrite(substr_ch);
  // handle the case where it is purely characters
  for (const Node& r : disj)
  {
    Assert(r.getKind() != REGEXP_UNION);
    Assert(r.getKind() != REGEXP_SIGMA);
    lenOnePeriod = false;
    // lenOnePeriod is true if this regular expression is a single character
    // regular expression
    if (r.getKind() == STRING_TO_REGEXP)
    {
      Node s = r[0];
      if (s.isConst() && s.getConst<String>().size() == 1)
      {
        lenOnePeriod = true;
      }
    }
    else if (r.getKind() == REGEXP_RANGE)
    {
      lenOnePeriod = true;
    }
    if (!lenOnePeriod)
    {
      break;
    }
    else
    {
      Node regexp_ch = nm->mkNode(STRING_IN_REGEXP, substr_ch, r);
      regexp_ch = Rewriter::rewrite(regexp_ch);
      Assert(regexp_ch.getKind() != STRING_IN_REGEXP);
      char_constraints.push_back(regexp_ch);
    }
  }
  if (lenOnePeriod)
  {
    Assert(!char_constraints.empty());
    Node bound = nm->mkNode(
        AND, nm->mkNode(LEQ, d_zero, index), nm->mkNode(LT, index, lenx));
    Node conc = char_constraints.size() == 1 ? char_constraints[0]
                                             : nm->mkNode(OR, char_constraints);
    Node body = nm->mkNode(OR, bound.negate(), conc);
    Node bvl = nm->mkNode(BOUND_VAR_LIST, index);
    Node res = nm->mkNode(FORALL, bvl, body);
    // e.g.
    //   x in (re.* (re.union "A" "B" )) --->
    //   forall k. 0<=k<len(x) => (substr(x,k,1) in "A" OR substr(x,k,1) in "B")
    return returnElim(atom, res, "star-char");
  }
  // otherwise, for stars of constant length these are periodic
  if (disj.size() == 1)
  {
    Node r = disj[0];
    if (r.getKind() == STRING_TO_REGEXP)
    {
      Node s = r[0];
      if (s.isConst())
      {
        Node lens = nm->mkNode(STRING_LENGTH, s);
        lens = Rewriter::rewrite(lens);
        Assert(lens.isConst());
        Assert(lens.getConst<Rational>().sgn() > 0);
        std::vector<Node> conj;
        // lens is a positive constant, so it is safe to use total div/mod here.
        Node bound = nm->mkNode(
            AND,
            nm->mkNode(LEQ, d_zero, index),
            nm->mkNode(LT, index, nm->mkNode(INTS_DIVISION_TOTAL, lenx, lens)));
        Node conc =
            nm->mkNode(STRING_SUBSTR, x, nm->mkNode(MULT, index, lens), lens)
                .eqNode(s);
        Node body = nm->mkNode(OR, bound.negate(), conc);
        Node bvl = nm->mkNode(BOUND_VAR_LIST, index);
        Node res = nm->mkNode(FORALL, bvl, body);
        res = nm->mkNode(
            AND,
            nm->mkNode(INTS_MODULUS_TOTAL, lenx, lens).eqNode(d_zero),
            res);
        // e.g.
        //    x in ("abc")* --->
        //    forall k. 0 <= k < (len( x ) div 3) => substr(x,3*k,3) = "abc" ^
        //    len(x) mod 3 = 0
        return returnElim(atom, res, "star-constant");
      }
    }
  }
  return Node::null();
}

Node RegExpElimination::returnElim(Node atom, Node atomElim, const char* id)
{
  Trace("re-elim") << "re-elim: " << atom << " to " << atomElim << " by " << id
                   << "." << std::endl;
  return atomElim;
}
