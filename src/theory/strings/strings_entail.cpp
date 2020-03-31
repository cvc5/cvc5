/*********************                                                        */
/*! \file strings_entail.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of entailment tests involving strings.
 **/

#include "theory/strings/string_entail.h"

#include "expr/node_builder.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {
  
Node StringsEntail::checkContains(Node a, Node b, bool fullRewriter)
{
  NodeManager* nm = NodeManager::currentNM();
  Node ctn = nm->mkNode(kind::STRING_STRCTN, a, b);

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
      ctn = rewriteContains(ctn);
    } while (prev != ctn && ctn.getKind() == kind::STRING_STRCTN);
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
  return ArithEntail::check(one, len) && (!strict || ArithEntail::check(len, true));
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
  NodeManager* nm = NodeManager::currentNM();
  Node res;
  while (res.isNull())
  {
    switch (n.getKind())
    {
      case kind::STRING_STRREPL:
      {
        Node empty = nm->mkConst(::CVC4::String(""));
        if (n[0] == empty)
        {
          // (str.replace "" x y) --> y
          n = n[2];
          break;
        }

        if (checkEntailLengthOne(n[0]) && n[2] == empty)
        {
          // (str.replace "A" x "") --> "A"
          res = n[0];
          break;
        }

        res = n;
        break;
      }
      case kind::STRING_SUBSTR:
      {
        if (checkEntailLengthOne(n[0]))
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
  Node emp = nm->mkConst(String(""));
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


}
}
}
