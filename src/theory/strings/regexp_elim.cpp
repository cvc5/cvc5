/*********************                                                        */
/*! \file regexp_elim.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniques for eliminating regular expressions
 **
 **/

#include "theory/strings/regexp_elim.h"

#include "options/strings_options.h"
#include "theory/strings/theory_strings_rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

RegExpElimination::RegExpElimination()
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
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
  // memberships of the form x in re.++ * s1 * ... * sn *, where * are
  // any number of repetitions (exact or indefinite) of REGEXP_SIGMA.
  Trace("re-elim-debug") << "Try re concat with gaps " << atom << std::endl;
  std::vector<Node> children;
  TheoryStringsRewriter::getConcat(re, children);
  bool success = true;
  std::vector<Node> sep_children;
  std::vector<int> gap_minsize;
  std::vector<bool> gap_exact;
  // the first gap is initially strict zero
  gap_minsize.push_back(0);
  gap_exact.push_back(true);
  unsigned nchildren = children.size();
  for (unsigned i = 0; i < nchildren; i++)
  {
    Node c = children[i];
    Trace("re-elim-debug") << "  " << c << std::endl;
    success = false;
    if (c.getKind() == STRING_TO_REGEXP)
    {
      success = true;
      sep_children.push_back(c[0]);
      // the next gap is initially strict zero
      gap_minsize.push_back(0);
      gap_exact.push_back(true);
    }
    else if (c.getKind() == REGEXP_STAR && c[0].getKind() == REGEXP_SIGMA)
    {
      // found a gap of any size
      success = true;
      gap_exact[gap_exact.size() - 1] = false;
    }
    else if (c.getKind() == REGEXP_SIGMA)
    {
      // add one to the minimum size of the gap
      success = true;
      gap_minsize[gap_minsize.size() - 1]++;
    }
    if (!success)
    {
      Trace("re-elim-debug") << "...cannot handle " << c << std::endl;
      break;
    }
  }
  if (success)
  {
    std::vector<Node> conj;
    // The following constructs a set of constraints that encodes that a
    // set of string terms are found, in order, in string x.
    // prev_end stores the current (symbolic) index in x that we are
    // searching.
    Node prev_end = d_zero;
    unsigned gap_minsize_end = gap_minsize.back();
    bool gap_exact_end = gap_exact.back();
    std::vector<Node> non_greedy_find_vars;
    for (unsigned i = 0, size = sep_children.size(); i < size; i++)
    {
      Node sc = sep_children[i];
      if (gap_minsize[i] > 0)
      {
        // the gap to this child is at least gap_minsize[i]
        prev_end =
            nm->mkNode(PLUS, prev_end, nm->mkConst(Rational(gap_minsize[i])));
      }
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
            success = false;
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
      // if applicable, process the last gap
      if (i == (size - 1))
      {
        if (gap_exact_end)
        {
          // substring relative to the end
          Node curr = nm->mkNode(MINUS, lenx, lensc);
          if (gap_minsize_end > 0)
          {
            curr =
                nm->mkNode(MINUS, curr, nm->mkConst(Rational(gap_minsize_end)));
          }
          Node ss = nm->mkNode(STRING_SUBSTR, x, curr, lensc);
          conj.push_back(ss.eqNode(sc));
        }
        else if (gap_minsize_end > 0)
        {
          Node fit = nm->mkNode(
              LEQ,
              nm->mkNode(
                  PLUS, prev_end, nm->mkConst(Rational(gap_minsize_end))),
              lenx);
          conj.push_back(fit);
        }
      }
    }
    if (success)
    {
      Node res = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      // process the non-greedy find variables
      if (!non_greedy_find_vars.empty())
      {
        std::vector<Node> children;
        for (const Node& v : non_greedy_find_vars)
        {
          Node bound = nm->mkNode(
              AND, nm->mkNode(LEQ, d_zero, v), nm->mkNode(LT, v, lenx));
          children.push_back(bound);
        }
        children.push_back(res);
        Node body = nm->mkNode(AND, children);
        Node bvl = nm->mkNode(BOUND_VAR_LIST, non_greedy_find_vars);
        res = nm->mkNode(EXISTS, bvl, body);
      }
      return returnElim(atom, res, "concat-with-gaps");
    }
  }
  
  if (!options::regExpElimAgg())
  {
    return Node::null();
  }
  // only aggressive rewrites below here
  
  // if the first or last child is constant string, split
  Node sStartIndex = d_zero;
  Node sLength = lenx;
  std::vector< Node > sConstraints;
  std::vector< Node > rexpElimChildren;
  for (unsigned r=0; r<2; r++)
  {
    unsigned index = r==0 ? 0 : nchildren-1;
    Node c = children[index];
    if( c.getKind()==STRING_TO_REGEXP )
    {
      Node s = c[0];
      Node lens = nm->mkNode(STRING_LENGTH,s);
      Node sss = r==0 ? d_zero : nm->mkNode(MINUS,lenx,lens);
      Node ss = nm->mkNode(STRING_SUBSTR,x,sss,lens);
      sConstraints.push_back(ss.eqNode(s));
      if( r==0 )
      {
        sStartIndex = lens;
      }
      sLength = nm->mkNode( MINUS, sLength, lens );
    }
    if(r==1 && !sConstraints.empty() )
    {
      // add the middle children
      for(unsigned i=1; i<(nchildren-1); i++ )
      {
        rexpElimChildren.push_back(children[i]);
      }
    }
    if( c.getKind()!=STRING_TO_REGEXP )
    {
      rexpElimChildren.push_back(c);
    }
  }
  if (!sConstraints.empty()) 
  {
    Node ss = nm->mkNode(STRING_SUBSTR,x,sStartIndex,sLength);
    Assert( !rexpElimChildren.empty() );
    Node regElim = TheoryStringsRewriter::mkConcat(REGEXP_CONCAT,rexpElimChildren);
    sConstraints.push_back( nm->mkNode(STRING_IN_REGEXP,ss,regElim) );
    Node ret = nm->mkNode(AND,sConstraints);
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
                       nm->mkNode(LT, k, nm->mkNode(MINUS, lenx, lens)));
        echildren.push_back(bound);
      }
      Node substrEq = nm->mkNode(STRING_SUBSTR, x, k, lens).eqNode(s);
      echildren.push_back(substrEq);
      if (i > 0)
      {
        std::vector<Node> rprefix;
        rprefix.insert(rprefix.end(), children.begin(), children.begin() + i);
        Node rpn = TheoryStringsRewriter::mkConcat(REGEXP_CONCAT, rprefix);
        Node substrPrefix = nm->mkNode(
            STRING_IN_REGEXP, nm->mkNode(STRING_SUBSTR, x, d_zero, k), rpn);
        echildren.push_back(substrPrefix);
      }
      if (i + 1 < nchildren)
      {
        std::vector<Node> rsuffix;
        rsuffix.insert(rsuffix.end(), children.begin() + i + 1, children.end());
        Node rps = TheoryStringsRewriter::mkConcat(REGEXP_CONCAT, rsuffix);
        Node ks = nm->mkNode(PLUS, k, lens);
        Node substrSuffix = nm->mkNode(
            STRING_IN_REGEXP,
            nm->mkNode(STRING_SUBSTR, x, ks, nm->mkNode(MINUS, lenx, ks)),
            rps);
        echildren.push_back(substrSuffix);
      }
      Node body = nm->mkNode(AND, echildren);
      if (!k.isNull())
      {
        Node bvl = nm->mkNode(BOUND_VAR_LIST, k);
        body = nm->mkNode(EXISTS, bvl, body);
      }
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
  bool success = true;
  std::vector<Node> char_constraints;
  Node index = nm->mkBoundVar(nm->integerType());
  Node substr_ch = nm->mkNode(STRING_SUBSTR, x, index, d_one);
  substr_ch = Rewriter::rewrite(substr_ch);
  // handle the case where it is purely characters
  for (const Node& r : disj)
  {
    Assert(r.getKind() != REGEXP_SIGMA);
    success = false;
    // success is true if the constraint
    if (r.getKind() == STRING_TO_REGEXP)
    {
      Node s = r[0];
      if (s.isConst() && s.getConst<String>().size() == 1)
      {
        success = true;
      }
    }
    else if (r.getKind() == REGEXP_RANGE)
    {
      success = true;
    }
    if (!success)
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
  if (success)
  {
    Assert(!char_constraints.empty());
    Node bound = nm->mkNode(
        AND, nm->mkNode(LEQ, d_zero, index), nm->mkNode(LT, index, lenx));
    Node conc = char_constraints.size() == 1 ? char_constraints[0]
                                             : nm->mkNode(OR, char_constraints);
    Node body = nm->mkNode(OR, bound.negate(), conc);
    Node bvl = nm->mkNode(BOUND_VAR_LIST, index);
    Node res = nm->mkNode(FORALL, bvl, body);
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
        Assert(lens.isConst());
        std::vector<Node> conj;
        Node bound = nm->mkNode(
            AND,
            nm->mkNode(LEQ, d_zero, index),
            nm->mkNode(LT, index, nm->mkNode(INTS_DIVISION, lenx, lens)));
        Node conc =
            nm->mkNode(STRING_SUBSTR, x, nm->mkNode(MULT, index, lens), lens)
                .eqNode(s);
        Node body = nm->mkNode(OR, bound.negate(), conc);
        Node bvl = nm->mkNode(BOUND_VAR_LIST, index);
        Node res = nm->mkNode(FORALL, bvl, body);
        res = nm->mkNode(
            AND, nm->mkNode(INTS_MODULUS, lenx, lens).eqNode(d_zero), res);
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
