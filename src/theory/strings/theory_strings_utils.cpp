/*********************                                                        */
/*! \file theory_strings_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory strings.
 **
 ** Util functions for theory strings.
 **/

#include "theory/strings/theory_strings_utils.h"

#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/word.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {
namespace utils {

uint32_t getAlphabetCardinality()
{
  if (options::stdPrintASCII())
  {
    Assert(128 <= String::num_codes());
    return 128;
  }
  Assert(256 <= String::num_codes());
  return 256;
}

Node mkAnd(const std::vector<Node>& a)
{
  std::vector<Node> au;
  for (const Node& ai : a)
  {
    if (std::find(au.begin(), au.end(), ai) == au.end())
    {
      au.push_back(ai);
    }
  }
  if (au.empty())
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (au.size() == 1)
  {
    return au[0];
  }
  return NodeManager::currentNM()->mkNode(AND, au);
}

void flattenOp(Kind k, Node n, std::vector<Node>& conj)
{
  if (n.getKind() != k)
  {
    // easy case, just add to conj if non-duplicate
    if (std::find(conj.begin(), conj.end(), n) == conj.end())
    {
      conj.push_back(n);
    }
    return;
  }
  // otherwise, traverse
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == k)
      {
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else if (std::find(conj.begin(), conj.end(), cur) == conj.end())
      {
        conj.push_back(cur);
      }
    }
  } while (!visit.empty());
}

void getConcat(Node n, std::vector<Node>& c)
{
  Kind k = n.getKind();
  if (k == STRING_CONCAT || k == REGEXP_CONCAT)
  {
    for (const Node& nc : n)
    {
      c.push_back(nc);
    }
  }
  else
  {
    c.push_back(n);
  }
}

Node mkConcat(const std::vector<Node>& c, TypeNode tn)
{
  Assert(tn.isStringLike() || tn.isRegExp());
  if (c.empty())
  {
    Assert(tn.isStringLike());
    return Word::mkEmptyWord(tn);
  }
  else if (c.size() == 1)
  {
    return c[0];
  }
  Kind k = tn.isStringLike() ? STRING_CONCAT : REGEXP_CONCAT;
  return NodeManager::currentNM()->mkNode(k, c);
}

Node mkNConcat(Node n1, Node n2)
{
  return Rewriter::rewrite(
      NodeManager::currentNM()->mkNode(STRING_CONCAT, n1, n2));
}

Node mkNConcat(Node n1, Node n2, Node n3)
{
  return Rewriter::rewrite(
      NodeManager::currentNM()->mkNode(STRING_CONCAT, n1, n2, n3));
}

Node mkNConcat(const std::vector<Node>& c, TypeNode tn)
{
  return Rewriter::rewrite(mkConcat(c, tn));
}

Node mkNLength(Node t)
{
  return Rewriter::rewrite(NodeManager::currentNM()->mkNode(STRING_LENGTH, t));
}

Node getConstantComponent(Node t)
{
  if (t.getKind() == STRING_TO_REGEXP)
  {
    return t[0].isConst() ? t[0] : Node::null();
  }
  return t.isConst() ? t : Node::null();
}

Node getConstantEndpoint(Node e, bool isSuf)
{
  Kind ek = e.getKind();
  if (ek == STRING_IN_REGEXP)
  {
    e = e[1];
    ek = e.getKind();
  }
  if (ek == STRING_CONCAT || ek == REGEXP_CONCAT)
  {
    return getConstantComponent(e[isSuf ? e.getNumChildren() - 1 : 0]);
  }
  return getConstantComponent(e);
}


Node splitConstant(Node a, Node b, int& index, bool isRev)
{
  Assert(a.isConst() && b.isConst());
  size_t lenA = Word::getLength(a);
  size_t lenB = Word::getLength(b);
  index = lenA <= lenB ? 1 : 0;
  size_t len_short = index == 1 ? lenA : lenB;
  bool cmp =
      isRev ? a.getConst<String>().rstrncmp(b.getConst<String>(), len_short)
            : a.getConst<String>().strncmp(b.getConst<String>(), len_short);
  if (cmp)
  {
    Node l = index == 0 ? a : b;
    if (isRev)
    {
      int new_len = l.getConst<String>().size() - len_short;
      return Word::substr(l, 0, new_len);
    }
    else
    {
      return Word::substr(l, len_short);
    }
  }
  // not the same prefix/suffix
  return Node::null();
}

bool canConstantContainConcat(Node c,
                                                 Node n,
                                                 int& firstc,
                                                 int& lastc)
{
  Assert(c.isConst());
  CVC4::String t = c.getConst<String>();
  const std::vector<unsigned>& tvec = t.getVec();
  Assert(n.getKind() == kind::STRING_CONCAT);
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
      CVC4::String s = n[i].getConst<String>();
      size_t new_pos = t.find(s, pos);
      if (new_pos == std::string::npos)
      {
        return false;
      }
      else
      {
        pos = new_pos + s.size();
      }
    }
    else if (n[i].getKind() == kind::STRING_ITOS && checkEntailArith(n[i][0]))
    {
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

bool canConstantContainList(Node c,
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

bool stripSymbolicLength(std::vector<Node>& n1,
                                            std::vector<Node>& nr,
                                            int dir,
                                            Node& curr)
{
  Assert(dir == 1 || dir == -1);
  Assert(nr.empty());
  Node zero = NodeManager::currentNM()->mkConst(CVC4::Rational(0));
  bool ret = false;
  bool success;
  unsigned sindex = 0;
  do
  {
    Assert(!curr.isNull());
    success = false;
    if (curr != zero && sindex < n1.size())
    {
      unsigned sindex_use = dir == 1 ? sindex : ((n1.size() - 1) - sindex);
      if (n1[sindex_use].isConst())
      {
        // could strip part of a constant
        Node lowerBound = getConstantArithBound(Rewriter::rewrite(curr));
        if (!lowerBound.isNull())
        {
          Assert(lowerBound.isConst());
          Rational lbr = lowerBound.getConst<Rational>();
          if (lbr.sgn() > 0)
          {
            Assert(checkEntailArith(curr, true));
            CVC4::String s = n1[sindex_use].getConst<String>();
            Node ncl =
                NodeManager::currentNM()->mkConst(CVC4::Rational(s.size()));
            Node next_s =
                NodeManager::currentNM()->mkNode(kind::MINUS, lowerBound, ncl);
            next_s = Rewriter::rewrite(next_s);
            Assert(next_s.isConst());
            // we can remove the entire constant
            if (next_s.getConst<Rational>().sgn() >= 0)
            {
              curr = Rewriter::rewrite(
                  NodeManager::currentNM()->mkNode(kind::MINUS, curr, ncl));
              success = true;
              sindex++;
            }
            else
            {
              // we can remove part of the constant
              // lower bound minus the length of a concrete string is negative,
              // hence lowerBound cannot be larger than long max
              Assert(lbr < Rational(String::maxSize()));
              curr = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                  kind::MINUS, curr, lowerBound));
              uint32_t lbsize = lbr.getNumerator().toUnsignedInt();
              Assert(lbsize < s.size());
              if (dir == 1)
              {
                // strip partially from the front
                nr.push_back(
                    NodeManager::currentNM()->mkConst(s.prefix(lbsize)));
                n1[sindex_use] = NodeManager::currentNM()->mkConst(
                    s.suffix(s.size() - lbsize));
              }
              else
              {
                // strip partially from the back
                nr.push_back(
                    NodeManager::currentNM()->mkConst(s.suffix(lbsize)));
                n1[sindex_use] = NodeManager::currentNM()->mkConst(
                    s.prefix(s.size() - lbsize));
              }
              ret = true;
            }
            Assert(checkEntailArith(curr));
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
            kind::MINUS,
            curr,
            NodeManager::currentNM()->mkNode(kind::STRING_LENGTH,
                                             n1[sindex_use]));
        next_s = Rewriter::rewrite(next_s);
        if (checkEntailArith(next_s))
        {
          success = true;
          curr = next_s;
          sindex++;
        }
      }
    }
  } while (success);
  if (sindex > 0)
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

int componentContains(std::vector<Node>& n1,
                                         std::vector<Node>& n2,
                                         std::vector<Node>& nb,
                                         std::vector<Node>& ne,
                                         bool computeRemainder,
                                         int remainderDir)
{
  Assert(nb.empty());
  Assert(ne.empty());
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
            n1[i] = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                kind::STRING_CONCAT, n1[i], n1re));
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
            n1[i] = Rewriter::rewrite(NodeManager::currentNM()->mkNode(
                kind::STRING_CONCAT, n1rb, n1[i]));
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

bool componentContainsBase(
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
      if (n2.getKind() == kind::STRING_SUBSTR)
      {
        if (n2[0] == n1)
        {
          bool success = true;
          Node start_pos = n2[1];
          Node end_pos = nm->mkNode(kind::PLUS, n2[1], n2[2]);
          Node len_n2s = nm->mkNode(kind::STRING_LENGTH, n2[0]);
          if (dir == 1)
          {
            // To be a suffix, start + length must be greater than
            // or equal to the length of the string.
            success = checkEntailArith(end_pos, len_n2s);
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
              if (!checkEntailArith(start_pos) || !checkEntailArith(end_pos))
              {
                return false;
              }
              if (dir != 1)
              {
                n1rb = nm->mkNode(kind::STRING_SUBSTR,
                                  n2[0],
                                  nm->mkConst(Rational(0)),
                                  start_pos);
              }
              if (dir != -1)
              {
                n1re = nm->mkNode(kind::STRING_SUBSTR, n2[0], end_pos, len_n2s);
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
          Node xCtnW = checkEntailContains(n1[0], n2);
          if (!xCtnW.isNull() && xCtnW.getConst<bool>())
          {
            Node zCtnW = checkEntailContains(n1[2], n2);
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

bool stripConstantEndpoints(std::vector<Node>& n1,
                                               std::vector<Node>& n2,
                                               std::vector<Node>& nb,
                                               std::vector<Node>& ne,
                                               int dir)
{
  Assert(nb.empty());
  Assert(ne.empty());

  NodeManager* nm = NodeManager::currentNM();
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

      if (n1cmp.isConst() && n1cmp.getConst<String>().size() == 0)
      {
        return false;
      }

      std::vector<Node> sss;
      std::vector<Node> sls;
      n1cmp = decomposeSubstrChain(n1cmp, sss, sls);
      Trace("strings-rewrite-debug2")
          << "stripConstantEndpoints : Compare " << n1cmp << " " << n2[index1]
          << ", dir = " << dir << std::endl;
      if (n1cmp.isConst())
      {
        CVC4::String s = n1cmp.getConst<String>();
        // overlap is an overapproximation of the number of characters
        // n2[index1] can match in s
        unsigned overlap = s.size();
        if (n2[index1].isConst())
        {
          CVC4::String t = n2[index1].getConst<String>();
          std::size_t ret = r == 0 ? s.find(t) : s.rfind(t);
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
              overlap = r == 0 ? s.overlap(t) : t.overlap(s);
            }
            else
            {
              // if we are looking at a substring, we can remove the component
              // if there is no overlap
              //   e.g. str.contains( str.++( str.substr( "c", i, j ), x), "a" )
              //        --> str.contains( x, "a" )
              removeComponent = ((r == 0 ? s.overlap(t) : t.overlap(s)) == 0);
            }
          }
          else if (sss.empty())  // only if not substr
          {
            Assert(ret < s.size());
            // can strip off up to the find position, e.g.
            // str.contains( str.++( "abc", x ), str.++( "b", y ) ) -->
            // str.contains( str.++( "bc", x ), str.++( "b", y ) ),
            // and
            // str.contains( str.++( x, "abbd" ), str.++( y, "b" ) ) -->
            // str.contains( str.++( x, "abb" ), str.++( y, "b" ) )
            overlap = s.size() - ret;
          }
        }
        else
        {
          // inconclusive
        }
        // process the overlap
        if (overlap < s.size())
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
              nb.push_back(nm->mkConst(s.prefix(s.size() - overlap)));
              n1[index0] = nm->mkConst(s.suffix(overlap));
            }
            else
            {
              ne.push_back(nm->mkConst(s.suffix(s.size() - overlap)));
              n1[index0] = nm->mkConst(s.prefix(overlap));
            }
          }
        }
      }
      else if (n1cmp.getKind() == kind::STRING_ITOS)
      {
        if (n2[index1].isConst())
        {
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

Node canonicalStrForSymbolicLength(Node len, TypeNode stype)
{
  NodeManager* nm = NodeManager::currentNM();

  Node res;
  if (len.getKind() == kind::CONST_RATIONAL)
  {
    // c -> "A" repeated c times
    Rational ratLen = len.getConst<Rational>();
    Assert(ratLen.getDenominator() == 1);
    Integer intLen = ratLen.getNumerator();
    uint32_t u = intLen.getUnsignedInt();
    if (stype.isString())
    {
      res = nm->mkConst(String(std::string(u, 'A')));
    }
    else
    {
      Unimplemented() << "canonicalStrForSymbolicLength for non-string";
    }
  }
  else if (len.getKind() == kind::PLUS)
  {
    // x + y -> norm(x) + norm(y)
    NodeBuilder<> concatBuilder(kind::STRING_CONCAT);
    for (const auto& n : len)
    {
      Node sn = canonicalStrForSymbolicLength(n, stype);
      if (sn.isNull())
      {
        return Node::null();
      }
      std::vector<Node> snChildren;
      utils::getConcat(sn, snChildren);
      concatBuilder.append(snChildren);
    }
    res = concatBuilder.constructNode();
  }
  else if (len.getKind() == kind::MULT && len.getNumChildren() == 2
           && len[0].isConst())
  {
    // c * x -> norm(x) repeated c times
    Rational ratReps = len[0].getConst<Rational>();
    Assert(ratReps.getDenominator() == 1);
    Integer intReps = ratReps.getNumerator();

    Node nRep = canonicalStrForSymbolicLength(len[1], stype);
    std::vector<Node> nRepChildren;
    utils::getConcat(nRep, nRepChildren);
    NodeBuilder<> concatBuilder(kind::STRING_CONCAT);
    for (size_t i = 0, reps = intReps.getUnsignedInt(); i < reps; i++)
    {
      concatBuilder.append(nRepChildren);
    }
    res = concatBuilder.constructNode();
  }
  else if (len.getKind() == kind::STRING_LENGTH)
  {
    // len(x) -> x
    res = len[0];
  }
  return res;
}

bool isUnboundedWildcard(const std::vector<Node>& rs, size_t start)
{
  size_t i = start;
  while (i < rs.size() && rs[i].getKind() == REGEXP_SIGMA)
  {
    i++;
  }

  if (i >= rs.size())
  {
    return false;
  }

  return rs[i].getKind() == REGEXP_STAR && rs[i][0].getKind() == REGEXP_SIGMA;
}

bool isSimpleRegExp(Node r)
{
  Assert(r.getType().isRegExp());

  std::vector<Node> v;
  utils::getConcat(r, v);
  for (const Node& n : v)
  {
    if (n.getKind() == STRING_TO_REGEXP)
    {
      if (!n[0].isConst())
      {
        return false;
      }
    }
    else if (n.getKind() != REGEXP_SIGMA
             && (n.getKind() != REGEXP_STAR || n[0].getKind() != REGEXP_SIGMA))
    {
      return false;
    }
  }
  return true;
}

void getRegexpComponents(Node r, std::vector<Node>& result)
{
  Assert(r.getType().isRegExp());

  NodeManager* nm = NodeManager::currentNM();
  if (r.getKind() == REGEXP_CONCAT)
  {
    for (const Node& n : r)
    {
      getRegexpComponents(n, result);
    }
  }
  else if (r.getKind() == STRING_TO_REGEXP && r[0].isConst())
  {
    size_t rlen = Word::getLength(r[0]);
    for (size_t i = 0; i < rlen; i++)
    {
      result.push_back(nm->mkNode(STRING_TO_REGEXP, Word::substr(r[0], i, 1)));
    }
  }
  else
  {
    result.push_back(r);
  }
}

void printConcat(std::ostream& out, std::vector<Node>& n)
{
  for (unsigned i = 0, nsize = n.size(); i < nsize; i++)
  {
    if (i > 0)
    {
      out << " ++ ";
    }
    out << n[i];
  }
}

void printConcatTrace(std::vector<Node>& n, const char* c)
{
  std::stringstream ss;
  printConcat(ss, n);
  Trace(c) << ss.str();
}

bool isStringKind(Kind k)
{
  return k == STRING_STOI || k == STRING_ITOS || k == STRING_TOLOWER
         || k == STRING_TOUPPER || k == STRING_LEQ || k == STRING_LT
         || k == STRING_FROM_CODE || k == STRING_TO_CODE;
}

TypeNode getOwnerStringType(Node n)
{
  TypeNode tn;
  Kind k = n.getKind();
  if (k == STRING_STRIDOF || k == STRING_LENGTH || k == STRING_STRCTN
      || k == STRING_PREFIX || k == STRING_SUFFIX)
  {
    // owning string type is the type of first argument
    tn = n[0].getType();
  }
  else if (isStringKind(k))
  {
    tn = NodeManager::currentNM()->stringType();
  }
  else
  {
    tn = n.getType();
  }
  AlwaysAssert(tn.isStringLike())
      << "Unexpected term in getOwnerStringType : " << n << ", type " << tn;
  return tn;
}

unsigned getRepeatAmount(TNode node)
{
  Assert(node.getKind() == REGEXP_REPEAT);
  return node.getOperator().getConst<RegExpRepeat>().d_repeatAmount;
}

unsigned getLoopMaxOccurrences(TNode node)
{
  Assert(node.getKind() == REGEXP_LOOP);
  return node.getOperator().getConst<RegExpLoop>().d_loopMaxOcc;
}

unsigned getLoopMinOccurrences(TNode node)
{
  Assert(node.getKind() == REGEXP_LOOP);
  return node.getOperator().getConst<RegExpLoop>().d_loopMinOcc;
}


Node getFixedLengthForRegexp(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == STRING_TO_REGEXP)
  {
    Node ret = nm->mkNode(STRING_LENGTH, n[0]);
    ret = Rewriter::rewrite(ret);
    if (ret.isConst())
    {
      return ret;
    }
  }
  else if (n.getKind() == REGEXP_SIGMA || n.getKind() == REGEXP_RANGE)
  {
    return nm->mkConst(Rational(1));
  }
  else if (n.getKind() == REGEXP_UNION || n.getKind() == REGEXP_INTER)
  {
    Node ret;
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull() || (!ret.isNull() && ret != flc))
      {
        return Node::null();
      }
      else if (ret.isNull())
      {
        // first time
        ret = flc;
      }
    }
    return ret;
  }
  else if (n.getKind() == REGEXP_CONCAT)
  {
    NodeBuilder<> nb(PLUS);
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull())
      {
        return flc;
      }
      nb << flc;
    }
    Node ret = nb.constructNode();
    ret = Rewriter::rewrite(ret);
    return ret;
  }
  return Node::null();
}


}  // namespace utils
}  // namespace strings
}  // namespace theory
}  // namespace CVC4
