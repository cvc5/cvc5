/*********************                                                        */
/*! \file strings_entail.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of entailment tests involving strings.
 **/

#include "theory/strings/strings_entail.h"

#include "expr/node_builder.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

StringsEntail::StringsEntail(SequencesRewriter& rewriter) : d_rewriter(rewriter)
{
}

bool StringsEntail::canConstantContainConcat(Node c,
                                             Node n,
                                             int& firstc,
                                             int& lastc)
{
  Assert(c.isConst());
  Assert(n.getKind() == STRING_CONCAT);
  // must find constant components in order
  size_t pos = 0;
  firstc = -1;
  lastc = -1;
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    if (n[i].isConst())
    {
      firstc = firstc == -1 ? i : firstc;
      lastc = i;
      size_t new_pos = Word::find(c, n[i], pos);
      if (new_pos == std::string::npos)
      {
        return false;
      }
      else
      {
        pos = new_pos + Word::getLength(n[i]);
      }
    }
    else if (n[i].getKind() == STRING_ITOS && ArithEntail::check(n[i][0]))
    {
      Assert(c.getType().isString());  // string-only
      const std::vector<unsigned>& tvec = c.getConst<String>().getVec();
      // find the first occurrence of a digit starting at pos
      while (pos < tvec.size() && !String::isDigit(tvec[pos]))
      {
        pos++;
      }
      if (pos == tvec.size())
      {
        return false;
      }
      // must consume at least one digit here
      pos++;
    }
  }
  return true;
}

bool StringsEntail::canConstantContainList(Node c,
                                           std::vector<Node>& l,
                                           int& firstc,
                                           int& lastc)
{
  Assert(c.isConst());
  // must find constant components in order
  size_t pos = 0;
  firstc = -1;
  lastc = -1;
  for (unsigned i = 0; i < l.size(); i++)
  {
    if (l[i].isConst())
    {
      firstc = firstc == -1 ? i : firstc;
      lastc = i;
      size_t new_pos = Word::find(c, l[i], pos);
      if (new_pos == std::string::npos)
      {
        return false;
      }
      else
      {
        pos = new_pos + Word::getLength(l[i]);
      }
    }
  }
  return true;
}

bool StringsEntail::stripSymbolicLength(std::vector<Node>& n1,
                                        std::vector<Node>& nr,
                                        int dir,
                                        Node& curr,
                                        bool strict)
{
  Assert(dir == 1 || dir == -1);
  Assert(nr.empty());
  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConst(CVC4::Rational(0));
  bool ret = false;
  bool success = true;
  unsigned sindex = 0;
  while (success && curr != zero && sindex < n1.size())
  {
    Assert(!curr.isNull());
    success = false;
    unsigned sindex_use = dir == 1 ? sindex : ((n1.size() - 1) - sindex);
    if (n1[sindex_use].isConst())
    {
      // could strip part of a constant
      Node lowerBound = ArithEntail::getConstantBound(Rewriter::rewrite(curr));
      if (!lowerBound.isNull())
      {
        Assert(lowerBound.isConst());
        Rational lbr = lowerBound.getConst<Rational>();
        if (lbr.sgn() > 0)
        {
          Assert(ArithEntail::check(curr, true));
          Node s = n1[sindex_use];
          size_t slen = Word::getLength(s);
          Node ncl = nm->mkConst(CVC4::Rational(slen));
          Node next_s = nm->mkNode(MINUS, lowerBound, ncl);
          next_s = Rewriter::rewrite(next_s);
          Assert(next_s.isConst());
          // we can remove the entire constant
          if (next_s.getConst<Rational>().sgn() >= 0)
          {
            curr = Rewriter::rewrite(nm->mkNode(MINUS, curr, ncl));
            success = true;
            sindex++;
          }
          else
          {
            // we can remove part of the constant
            // lower bound minus the length of a concrete string is negative,
            // hence lowerBound cannot be larger than long max
            Assert(lbr < Rational(String::maxSize()));
            curr = Rewriter::rewrite(nm->mkNode(MINUS, curr, lowerBound));
            uint32_t lbsize = lbr.getNumerator().toUnsignedInt();
            Assert(lbsize < slen);
            if (dir == 1)
            {
              // strip partially from the front
              nr.push_back(Word::prefix(s, lbsize));
              n1[sindex_use] = Word::suffix(s, slen - lbsize);
            }
            else
            {
              // strip partially from the back
              nr.push_back(Word::suffix(s, lbsize));
              n1[sindex_use] = Word::prefix(s, slen - lbsize);
            }
            ret = true;
          }
          Assert(ArithEntail::check(curr));
        }
        else
        {
          // we cannot remove the constant
        }
      }
    }
    else
    {
      Node next_s = NodeManager::currentNM()->mkNode(
          MINUS,
          curr,
          NodeManager::currentNM()->mkNode(STRING_LENGTH, n1[sindex_use]));
      next_s = Rewriter::rewrite(next_s);
      if (ArithEntail::check(next_s))
      {
        success = true;
        curr = next_s;
        sindex++;
      }
    }
  }
  if (sindex > 0 && (!strict || curr == zero))
  {
    if (dir == 1)
    {
      nr.insert(nr.begin(), n1.begin(), n1.begin() + sindex);
      n1.erase(n1.begin(), n1.begin() + sindex);
    }
    else
    {
      nr.insert(nr.end(), n1.end() - sindex, n1.end());
      n1.erase(n1.end() - sindex, n1.end());
    }
    ret = true;
  }
  return ret;
}

int StringsEntail::componentContains(std::vector<Node>& n1,
                                     std::vector<Node>& n2,
                                     std::vector<Node>& nb,
                                     std::vector<Node>& ne,
                                     bool computeRemainder,
                                     int remainderDir)
{
  Assert(nb.empty());
  Assert(ne.empty());
  Trace("strings-entail") << "Component contains: " << std::endl;
  Trace("strings-entail") << "n1 = " << n1 << std::endl;
  Trace("strings-entail") << "n2 = " << n2 << std::endl;
  // if n2 is a singleton, we can do optimized version here
  if (n2.size() == 1)
  {
    for (unsigned i = 0; i < n1.size(); i++)
    {
      Node n1rb;
      Node n1re;
      if (componentContainsBase(n1[i], n2[0], n1rb, n1re, 0, computeRemainder))
      {
        if (computeRemainder)
        {
          n1[i] = n2[0];
          if (remainderDir != -1)
          {
            if (!n1re.isNull())
            {
              ne.push_back(n1re);
            }
            ne.insert(ne.end(), n1.begin() + i + 1, n1.end());
            n1.erase(n1.begin() + i + 1, n1.end());
          }
          else if (!n1re.isNull())
          {
            n1[i] = Rewriter::rewrite(
                NodeManager::currentNM()->mkNode(STRING_CONCAT, n1[i], n1re));
          }
          if (remainderDir != 1)
          {
            nb.insert(nb.end(), n1.begin(), n1.begin() + i);
            n1.erase(n1.begin(), n1.begin() + i);
            if (!n1rb.isNull())
            {
              nb.push_back(n1rb);
            }
          }
          else if (!n1rb.isNull())
          {
            n1[i] = Rewriter::rewrite(
                NodeManager::currentNM()->mkNode(STRING_CONCAT, n1rb, n1[i]));
          }
        }
        return i;
      }
    }
  }
  else if (n1.size() >= n2.size())
  {
    unsigned diff = n1.size() - n2.size();
    for (unsigned i = 0; i <= diff; i++)
    {
      Node n1rb_first;
      Node n1re_first;
      // first component of n2 must be a suffix
      if (componentContainsBase(n1[i],
                                n2[0],
                                n1rb_first,
                                n1re_first,
                                1,
                                computeRemainder && remainderDir != 1))
      {
        Assert(n1re_first.isNull());
        for (unsigned j = 1; j < n2.size(); j++)
        {
          // are we in the last component?
          if (j + 1 == n2.size())
          {
            Node n1rb_last;
            Node n1re_last;
            // last component of n2 must be a prefix
            if (componentContainsBase(n1[i + j],
                                      n2[j],
                                      n1rb_last,
                                      n1re_last,
                                      -1,
                                      computeRemainder && remainderDir != -1))
            {
              Trace("strings-entail-debug")
                  << "Last remainder begin is " << n1rb_last << std::endl;
              Trace("strings-entail-debug")
                  << "Last remainder end is " << n1re_last << std::endl;
              Assert(n1rb_last.isNull());
              if (computeRemainder)
              {
                if (remainderDir != -1)
                {
                  if (!n1re_last.isNull())
                  {
                    ne.push_back(n1re_last);
                  }
                  ne.insert(ne.end(), n1.begin() + i + j + 1, n1.end());
                  n1.erase(n1.begin() + i + j + 1, n1.end());
                  n1[i + j] = n2[j];
                }
                if (remainderDir != 1)
                {
                  n1[i] = n2[0];
                  nb.insert(nb.end(), n1.begin(), n1.begin() + i);
                  n1.erase(n1.begin(), n1.begin() + i);
                  if (!n1rb_first.isNull())
                  {
                    nb.push_back(n1rb_first);
                  }
                }
              }
              Trace("strings-entail-debug") << "ne = " << ne << std::endl;
              Trace("strings-entail-debug") << "nb = " << nb << std::endl;
              Trace("strings-entail-debug") << "...return " << i << std::endl;
              return i;
            }
            else
            {
              break;
            }
          }
          else if (n1[i + j] != n2[j])
          {
            break;
          }
        }
      }
    }
  }
  return -1;
}

bool StringsEntail::componentContainsBase(
    Node n1, Node n2, Node& n1rb, Node& n1re, int dir, bool computeRemainder)
{
  Assert(n1rb.isNull());
  Assert(n1re.isNull());

  NodeManager* nm = NodeManager::currentNM();

  if (n1 == n2)
  {
    return true;
  }
  else
  {
    if (n1.isConst() && n2.isConst())
    {
      size_t len1 = Word::getLength(n1);
      size_t len2 = Word::getLength(n2);
      if (len2 < len1)
      {
        if (dir == 1)
        {
          if (Word::suffix(n1, len2) == n2)
          {
            if (computeRemainder)
            {
              n1rb = Word::prefix(n1, len1 - len2);
            }
            return true;
          }
        }
        else if (dir == -1)
        {
          if (Word::prefix(n1, len2) == n2)
          {
            if (computeRemainder)
            {
              n1re = Word::suffix(n1, len1 - len2);
            }
            return true;
          }
        }
        else
        {
          size_t f = Word::find(n1, n2);
          if (f != std::string::npos)
          {
            if (computeRemainder)
            {
              if (f > 0)
              {
                n1rb = Word::prefix(n1, f);
              }
              if (len1 > f + len2)
              {
                n1re = Word::suffix(n1, len1 - (f + len2));
              }
            }
            return true;
          }
        }
      }
    }
    else
    {
      // cases for:
      //   n1 = x   containing   n2 = substr( x, n2[1], n2[2] )
      if (n2.getKind() == STRING_SUBSTR)
      {
        if (n2[0] == n1)
        {
          bool success = true;
          Node start_pos = n2[1];
          Node end_pos = nm->mkNode(PLUS, n2[1], n2[2]);
          Node len_n2s = nm->mkNode(STRING_LENGTH, n2[0]);
          if (dir == 1)
          {
            // To be a suffix, start + length must be greater than
            // or equal to the length of the string.
            success = ArithEntail::check(end_pos, len_n2s);
          }
          else if (dir == -1)
          {
            // To be a prefix, must literally start at 0, since
            //   if we knew it started at <0, it should be rewritten to "",
            //   if we knew it started at 0, then n2[1] should be rewritten to
            //   0.
            success = start_pos.isConst()
                      && start_pos.getConst<Rational>().sgn() == 0;
          }
          if (success)
          {
            if (computeRemainder)
            {
              // we can only compute the remainder if start_pos and end_pos
              // are known to be non-negative.
              if (!ArithEntail::check(start_pos)
                  || !ArithEntail::check(end_pos))
              {
                return false;
              }
              if (dir != -1)
              {
                n1rb = nm->mkNode(
                    STRING_SUBSTR, n2[0], nm->mkConst(Rational(0)), start_pos);
              }
              if (dir != 1)
              {
                n1re = nm->mkNode(STRING_SUBSTR, n2[0], end_pos, len_n2s);
              }
            }
            return true;
          }
        }
      }

      if (!computeRemainder && dir == 0)
      {
        if (n1.getKind() == STRING_STRREPL)
        {
          // (str.contains (str.replace x y z) w) ---> true
          // if (str.contains x w) --> true and (str.contains z w) ---> true
          Node xCtnW = checkContains(n1[0], n2);
          if (!xCtnW.isNull() && xCtnW.getConst<bool>())
          {
            Node zCtnW = checkContains(n1[2], n2);
            if (!zCtnW.isNull() && zCtnW.getConst<bool>())
            {
              return true;
            }
          }
        }
      }
    }
  }
  return false;
}

bool StringsEntail::stripConstantEndpoints(std::vector<Node>& n1,
                                           std::vector<Node>& n2,
                                           std::vector<Node>& nb,
                                           std::vector<Node>& ne,
                                           int dir)
{
  Assert(nb.empty());
  Assert(ne.empty());
  bool changed = false;
  // for ( forwards, backwards ) direction
  for (unsigned r = 0; r < 2; r++)
  {
    if (dir == 0 || (r == 0 && dir == 1) || (r == 1 && dir == -1))
    {
      unsigned index0 = r == 0 ? 0 : n1.size() - 1;
      unsigned index1 = r == 0 ? 0 : n2.size() - 1;
      bool removeComponent = false;
      Node n1cmp = n1[index0];

      if (n1cmp.isConst() && Word::isEmpty(n1cmp))
      {
        return false;
      }

      std::vector<Node> sss;
      std::vector<Node> sls;
      n1cmp = utils::decomposeSubstrChain(n1cmp, sss, sls);
      Trace("strings-rewrite-debug2")
          << "stripConstantEndpoints : Compare " << n1cmp << " " << n2[index1]
          << ", dir = " << dir << std::endl;
      if (n1cmp.isConst())
      {
        Node s = n1cmp;
        size_t slen = Word::getLength(s);
        // overlap is an overapproximation of the number of characters
        // n2[index1] can match in s
        unsigned overlap = Word::getLength(s);
        if (n2[index1].isConst())
        {
          Node t = n2[index1];
          std::size_t ret = r == 0 ? Word::find(s, t) : Word::rfind(s, t);
          if (ret == std::string::npos)
          {
            if (n1.size() == 1)
            {
              // can remove everything
              //   e.g. str.contains( "abc", str.++( "ba", x ) ) -->
              //   str.contains( "", str.++( "ba", x ) )
              removeComponent = true;
            }
            else if (sss.empty())  // only if not substr
            {
              // check how much overlap there is
              // This is used to partially strip off the endpoint
              // e.g. str.contains( str.++( "abc", x ), str.++( "cd", y ) ) -->
              // str.contains( str.++( "c", x ), str.++( "cd", y ) )
              overlap = r == 0 ? Word::overlap(s, t) : Word::overlap(t, s);
            }
            else
            {
              // if we are looking at a substring, we can remove the component
              // if there is no overlap
              //   e.g. str.contains( str.++( str.substr( "c", i, j ), x), "a" )
              //        --> str.contains( x, "a" )
              removeComponent =
                  ((r == 0 ? Word::overlap(s, t) : Word::overlap(t, s)) == 0);
            }
          }
          else if (sss.empty())  // only if not substr
          {
            Assert(ret < slen);
            // can strip off up to the find position, e.g.
            // str.contains( str.++( "abc", x ), str.++( "b", y ) ) -->
            // str.contains( str.++( "bc", x ), str.++( "b", y ) ),
            // and
            // str.contains( str.++( x, "abbd" ), str.++( y, "b" ) ) -->
            // str.contains( str.++( x, "abb" ), str.++( y, "b" ) )
            overlap = slen - ret;
          }
        }
        else
        {
          // inconclusive
        }
        // process the overlap
        if (overlap < slen)
        {
          changed = true;
          if (overlap == 0)
          {
            removeComponent = true;
          }
          else
          {
            // can drop the prefix (resp. suffix) from the first (resp. last)
            // component
            if (r == 0)
            {
              nb.push_back(Word::prefix(s, slen - overlap));
              n1[index0] = Word::suffix(s, overlap);
            }
            else
            {
              ne.push_back(Word::suffix(s, slen - overlap));
              n1[index0] = Word::prefix(s, overlap);
            }
          }
        }
      }
      else if (n1cmp.getKind() == STRING_ITOS)
      {
        if (n2[index1].isConst())
        {
          Assert(n2[index1].getType().isString());  // string-only
          CVC4::String t = n2[index1].getConst<String>();
          if (n1.size() == 1)
          {
            // if n1.size()==1, then if n2[index1] is not a number, we can drop
            // the entire component
            //    e.g. str.contains( int.to.str(x), "123a45") --> false
            if (!t.isNumber())
            {
              removeComponent = true;
            }
          }
          else
          {
            const std::vector<unsigned>& tvec = t.getVec();
            Assert(tvec.size() > 0);

            // if n1.size()>1, then if the first (resp. last) character of
            // n2[index1]
            //  is not a digit, we can drop the entire component, e.g.:
            //    str.contains( str.++( int.to.str(x), y ), "a12") -->
            //    str.contains( y, "a12" )
            //    str.contains( str.++( y, int.to.str(x) ), "a0b") -->
            //    str.contains( y, "a0b" )
            unsigned i = r == 0 ? 0 : (tvec.size() - 1);
            if (!String::isDigit(tvec[i]))
            {
              removeComponent = true;
            }
          }
        }
      }
      if (removeComponent)
      {
        // can drop entire first (resp. last) component
        if (r == 0)
        {
          nb.push_back(n1[index0]);
          n1.erase(n1.begin(), n1.begin() + 1);
        }
        else
        {
          ne.push_back(n1[index0]);
          n1.pop_back();
        }
        if (n1.empty())
        {
          // if we've removed everything, just return (we will rewrite to false)
          return true;
        }
        else
        {
          changed = true;
        }
      }
    }
  }
  // TODO (#1180) : computing the maximal overlap in this function may be
  // important.
  // str.contains( str.++( str.to.int(x), str.substr(y,0,3) ), "2aaaa" ) --->
  // false
  //   ...since str.to.int(x) can contain at most 1 character from "2aaaa",
  //   leaving 4 characters
  //      which is larger that the upper bound for length of str.substr(y,0,3),
  //      which is 3.
  return changed;
}

Node StringsEntail::checkContains(Node a, Node b, bool fullRewriter)
{
  NodeManager* nm = NodeManager::currentNM();
  Node ctn = nm->mkNode(STRING_STRCTN, a, b);

  if (fullRewriter)
  {
    ctn = Rewriter::rewrite(ctn);
  }
  else
  {
    Node prev;
    do
    {
      prev = ctn;
      ctn = d_rewriter.rewriteContains(ctn);
    } while (prev != ctn && ctn.getKind() == STRING_STRCTN);
  }

  Assert(ctn.getType().isBoolean());
  return ctn.isConst() ? ctn : Node::null();
}

bool StringsEntail::checkNonEmpty(Node a)
{
  Node len = NodeManager::currentNM()->mkNode(STRING_LENGTH, a);
  len = Rewriter::rewrite(len);
  return ArithEntail::check(len, true);
}

bool StringsEntail::checkLengthOne(Node s, bool strict)
{
  NodeManager* nm = NodeManager::currentNM();
  Node one = nm->mkConst(Rational(1));
  Node len = nm->mkNode(STRING_LENGTH, s);
  len = Rewriter::rewrite(len);
  return ArithEntail::check(one, len)
         && (!strict || ArithEntail::check(len, true));
}

bool StringsEntail::checkMultisetSubset(Node a, Node b)
{
  std::vector<Node> avec;
  utils::getConcat(getMultisetApproximation(a), avec);
  std::vector<Node> bvec;
  utils::getConcat(b, bvec);

  std::map<Node, unsigned> num_nconst[2];
  std::map<Node, unsigned> num_const[2];
  for (unsigned j = 0; j < 2; j++)
  {
    std::vector<Node>& jvec = j == 0 ? avec : bvec;
    for (const Node& cc : jvec)
    {
      if (cc.isConst())
      {
        num_const[j][cc]++;
      }
      else
      {
        num_nconst[j][cc]++;
      }
    }
  }
  bool ms_success = true;
  for (std::pair<const Node, unsigned>& nncp : num_nconst[0])
  {
    if (nncp.second > num_nconst[1][nncp.first])
    {
      ms_success = false;
      break;
    }
  }
  if (ms_success)
  {
    // count the number of constant characters in the first argument
    std::map<Node, unsigned> count_const[2];
    std::vector<Node> chars;
    for (unsigned j = 0; j < 2; j++)
    {
      for (std::pair<const Node, unsigned>& ncp : num_const[j])
      {
        Node cn = ncp.first;
        Assert(cn.isConst());
        std::vector<Node> cnChars = Word::getChars(cn);
        for (const Node& ch : cnChars)
        {
          count_const[j][ch] += ncp.second;
          if (std::find(chars.begin(), chars.end(), ch) == chars.end())
          {
            chars.push_back(ch);
          }
        }
      }
    }
    Trace("strings-entail-ms-ss")
        << "For " << a << " and " << b << " : " << std::endl;
    for (const Node& ch : chars)
    {
      Trace("strings-entail-ms-ss") << "  # occurrences of substring ";
      Trace("strings-entail-ms-ss") << ch << " in arguments is ";
      Trace("strings-entail-ms-ss")
          << count_const[0][ch] << " / " << count_const[1][ch] << std::endl;
      if (count_const[0][ch] < count_const[1][ch])
      {
        return true;
      }
    }

    // TODO (#1180): count the number of 2,3,4,.. character substrings
    // for example:
    // str.contains( str.++( x, "cbabc" ), str.++( "cabbc", x ) ) ---> false
    // since the second argument contains more occurrences of "bb".
    // note this is orthogonal reasoning to inductive reasoning
    // via regular membership reduction in Liang et al CAV 2015.
  }
  return false;
}

Node StringsEntail::checkHomogeneousString(Node a)
{
  std::vector<Node> avec;
  utils::getConcat(getMultisetApproximation(a), avec);

  bool cValid = false;
  Node c;
  for (const Node& ac : avec)
  {
    if (ac.isConst())
    {
      std::vector<Node> acv = Word::getChars(ac);
      for (const Node& cc : acv)
      {
        if (!cValid)
        {
          cValid = true;
          c = cc;
        }
        else if (c != cc)
        {
          // Found a different character
          return Node::null();
        }
      }
    }
    else
    {
      // Could produce a different character
      return Node::null();
    }
  }

  if (!cValid)
  {
    return Word::mkEmptyWord(a.getType());
  }

  return c;
}

Node StringsEntail::getMultisetApproximation(Node a)
{
  NodeManager* nm = NodeManager::currentNM();
  if (a.getKind() == STRING_SUBSTR)
  {
    return a[0];
  }
  else if (a.getKind() == STRING_STRREPL)
  {
    return getMultisetApproximation(nm->mkNode(STRING_CONCAT, a[0], a[2]));
  }
  else if (a.getKind() == STRING_CONCAT)
  {
    NodeBuilder<> nb(STRING_CONCAT);
    for (const Node& ac : a)
    {
      nb << getMultisetApproximation(ac);
    }
    return nb.constructNode();
  }
  else
  {
    return a;
  }
}

Node StringsEntail::getStringOrEmpty(Node n)
{
  Node res;
  while (res.isNull())
  {
    switch (n.getKind())
    {
      case STRING_STRREPL:
      {
        if (Word::isEmpty(n[0]))
        {
          // (str.replace "" x y) --> y
          n = n[2];
          break;
        }

        if (checkLengthOne(n[0]) && Word::isEmpty(n[2]))
        {
          // (str.replace "A" x "") --> "A"
          res = n[0];
          break;
        }

        res = n;
        break;
      }
      case STRING_SUBSTR:
      {
        if (checkLengthOne(n[0]))
        {
          // (str.substr "A" x y) --> "A"
          res = n[0];
          break;
        }
        res = n;
        break;
      }
      default:
      {
        res = n;
        break;
      }
    }
  }
  return res;
}

Node StringsEntail::inferEqsFromContains(Node x, Node y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node emp = Word::mkEmptyWord(x.getType());
  Assert(x.getType() == y.getType());
  TypeNode stype = x.getType();

  Node xLen = nm->mkNode(STRING_LENGTH, x);
  std::vector<Node> yLens;
  if (y.getKind() != STRING_CONCAT)
  {
    yLens.push_back(nm->mkNode(STRING_LENGTH, y));
  }
  else
  {
    for (const Node& yi : y)
    {
      yLens.push_back(nm->mkNode(STRING_LENGTH, yi));
    }
  }

  std::vector<Node> zeroLens;
  if (x == emp)
  {
    // If x is the empty string, then all ys must be empty, too, and we can
    // skip the expensive checks. Note that this is just a performance
    // optimization.
    zeroLens.swap(yLens);
  }
  else
  {
    // Check if we can infer that str.len(x) <= str.len(y). If that is the
    // case, try to minimize the sum in str.len(x) <= str.len(y1) + ... +
    // str.len(yn) (where y = y1 ++ ... ++ yn) while keeping the inequality
    // true. The terms that can have length zero without making the inequality
    // false must be all be empty if (str.contains x y) is true.
    if (!ArithEntail::inferZerosInSumGeq(xLen, yLens, zeroLens))
    {
      // We could not prove that the inequality holds
      return Node::null();
    }
    else if (yLens.size() == y.getNumChildren())
    {
      // We could only prove that the inequality holds but not that any of the
      // ys must be empty
      return nm->mkNode(EQUAL, x, y);
    }
  }

  if (y.getKind() != STRING_CONCAT)
  {
    if (zeroLens.size() == 1)
    {
      // y is not a concatenation and we found that it must be empty, so just
      // return (= y "")
      Assert(zeroLens[0][0] == y);
      return nm->mkNode(EQUAL, y, emp);
    }
    else
    {
      Assert(yLens.size() == 1 && yLens[0][0] == y);
      return nm->mkNode(EQUAL, x, y);
    }
  }

  std::vector<Node> cs;
  for (const Node& yiLen : yLens)
  {
    Assert(std::find(y.begin(), y.end(), yiLen[0]) != y.end());
    cs.push_back(yiLen[0]);
  }

  NodeBuilder<> nb(AND);
  // (= x (str.++ y1' ... ym'))
  if (!cs.empty())
  {
    nb << nm->mkNode(EQUAL, x, utils::mkConcat(cs, stype));
  }
  // (= y1'' "") ... (= yk'' "")
  for (const Node& zeroLen : zeroLens)
  {
    Assert(std::find(y.begin(), y.end(), zeroLen[0]) != y.end());
    nb << nm->mkNode(EQUAL, zeroLen[0], emp);
  }

  // (and (= x (str.++ y1' ... ym')) (= y1'' "") ... (= yk'' ""))
  return nb.constructNode();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
