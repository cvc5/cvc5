/*********************                                                        */
/*! \file regexp_entail.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of entailment tests involving regular expressions
 **/

#include "theory/strings/regexp_entail.h"

#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node RegExpEntail::simpleRegexpConsume(std::vector<Node>& mchildren,
                                            std::vector<Node>& children,
                                            int dir)
{
  Trace("regexp-ext-rewrite-debug")
      << "Simple reg exp consume, dir=" << dir << ":" << std::endl;
  Trace("regexp-ext-rewrite-debug")
      << "  mchildren : " << mchildren << std::endl;
  Trace("regexp-ext-rewrite-debug") << "  children : " << children << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  unsigned tmin = dir < 0 ? 0 : dir;
  unsigned tmax = dir < 0 ? 1 : dir;
  // try to remove off front and back
  for (unsigned t = 0; t < 2; t++)
  {
    if (tmin <= t && t <= tmax)
    {
      bool do_next = true;
      while (!children.empty() && !mchildren.empty() && do_next)
      {
        do_next = false;
        Node xc = mchildren[mchildren.size() - 1];
        Node rc = children[children.size() - 1];
        Assert(rc.getKind() != REGEXP_CONCAT);
        Assert(xc.getKind() != STRING_CONCAT);
        if (rc.getKind() == STRING_TO_REGEXP)
        {
          if (xc == rc[0])
          {
            children.pop_back();
            mchildren.pop_back();
            do_next = true;
            Trace("regexp-ext-rewrite-debug") << "...strip equal" << std::endl;
          }
          else if (xc.isConst() && rc[0].isConst())
          {
            // split the constant
            int index;
            Node s = utils::splitConstant(xc, rc[0], index, t == 0);
            Trace("regexp-ext-rewrite-debug")
                << "CRE: Regexp const split : " << xc << " " << rc[0] << " -> "
                << s << " " << index << " " << t << std::endl;
            if (s.isNull())
            {
              Trace("regexp-ext-rewrite-debug")
                  << "...return false" << std::endl;
              return nm->mkConst(false);
            }
            else
            {
              Trace("regexp-ext-rewrite-debug")
                  << "...strip equal const" << std::endl;
              children.pop_back();
              mchildren.pop_back();
              if (index == 0)
              {
                mchildren.push_back(s);
              }
              else
              {
                children.push_back(nm->mkNode(STRING_TO_REGEXP, s));
              }
            }
            do_next = true;
          }
        }
        else if (xc.isConst())
        {
          // check for constants
          CVC4::String s = xc.getConst<String>();
          if (Word::isEmpty(xc))
          {
            Trace("regexp-ext-rewrite-debug") << "...ignore empty" << std::endl;
            // ignore and continue
            mchildren.pop_back();
            do_next = true;
          }
          else if (rc.getKind() == REGEXP_RANGE
                   || rc.getKind() == REGEXP_SIGMA)
          {
            std::vector<unsigned> ssVec;
            ssVec.push_back(t == 0 ? s.back() : s.front());
            CVC4::String ss(ssVec);
            if (testConstStringInRegExp(ss, 0, rc))
            {
              // strip off one character
              mchildren.pop_back();
              if (s.size() > 1)
              {
                if (t == 0)
                {
                  mchildren.push_back(nm->mkConst(
                      s.substr(0, s.size() - 1)));
                }
                else
                {
                  mchildren.push_back(
                      nm->mkConst(s.substr(1)));
                }
              }
              children.pop_back();
              do_next = true;
            }
            else
            {
              return nm->mkConst(false);
            }
          }
          else if (rc.getKind() == REGEXP_INTER
                   || rc.getKind() == REGEXP_UNION)
          {
            // see if any/each child does not work
            bool result_valid = true;
            Node result;
            Node emp_s = nm->mkConst(::CVC4::String(""));
            for (unsigned i = 0; i < rc.getNumChildren(); i++)
            {
              std::vector<Node> mchildren_s;
              std::vector<Node> children_s;
              mchildren_s.push_back(xc);
              utils::getConcat(rc[i], children_s);
              Node ret = simpleRegexpConsume(mchildren_s, children_s, t);
              if (!ret.isNull())
              {
                // one conjunct cannot be satisfied, return false
                if (rc.getKind() == REGEXP_INTER)
                {
                  return ret;
                }
              }
              else
              {
                if (children_s.empty())
                {
                  // if we were able to fully consume, store the result
                  Assert(mchildren_s.size() <= 1);
                  if (mchildren_s.empty())
                  {
                    mchildren_s.push_back(emp_s);
                  }
                  if (result.isNull())
                  {
                    result = mchildren_s[0];
                  }
                  else if (result != mchildren_s[0])
                  {
                    result_valid = false;
                  }
                }
                else
                {
                  result_valid = false;
                }
              }
            }
            if (result_valid)
            {
              if (result.isNull())
              {
                // all disjuncts cannot be satisfied, return false
                Assert(rc.getKind() == REGEXP_UNION);
                return nm->mkConst(false);
              }
              else
              {
                // all branches led to the same result
                children.pop_back();
                mchildren.pop_back();
                if (result != emp_s)
                {
                  mchildren.push_back(result);
                }
                do_next = true;
              }
            }
          }
          else if (rc.getKind() == REGEXP_STAR)
          {
            // check if there is no way that this star can be unrolled even once
            std::vector<Node> mchildren_s;
            mchildren_s.insert(
                mchildren_s.end(), mchildren.begin(), mchildren.end());
            if (t == 1)
            {
              std::reverse(mchildren_s.begin(), mchildren_s.end());
            }
            std::vector<Node> children_s;
            utils::getConcat(rc[0], children_s);
            Trace("regexp-ext-rewrite-debug")
                << "...recursive call on body of star" << std::endl;
            Node ret = simpleRegexpConsume(mchildren_s, children_s, t);
            if (!ret.isNull())
            {
              Trace("regexp-ext-rewrite-debug")
                  << "CRE : regexp star infeasable " << xc << " " << rc
                  << std::endl;
              children.pop_back();
              if (!children.empty())
              {
                Trace("regexp-ext-rewrite-debug") << "...continue" << std::endl;
                do_next = true;
              }
            }
            else
            {
              if (children_s.empty())
              {
                // check if beyond this, we can't do it or there is nothing
                // left, if so, repeat
                bool can_skip = false;
                if (children.size() > 1)
                {
                  std::vector<Node> mchildren_ss;
                  mchildren_ss.insert(
                      mchildren_ss.end(), mchildren.begin(), mchildren.end());
                  std::vector<Node> children_ss;
                  children_ss.insert(
                      children_ss.end(), children.begin(), children.end() - 1);
                  if (t == 1)
                  {
                    std::reverse(mchildren_ss.begin(), mchildren_ss.end());
                    std::reverse(children_ss.begin(), children_ss.end());
                  }
                  if (simpleRegexpConsume(mchildren_ss, children_ss, t)
                          .isNull())
                  {
                    can_skip = true;
                  }
                }
                if (!can_skip)
                {
                  Trace("regexp-ext-rewrite-debug")
                      << "...can't skip" << std::endl;
                  // take the result of fully consuming once
                  if (t == 1)
                  {
                    std::reverse(mchildren_s.begin(), mchildren_s.end());
                  }
                  mchildren.clear();
                  mchildren.insert(
                      mchildren.end(), mchildren_s.begin(), mchildren_s.end());
                  do_next = true;
                }
                else
                {
                  Trace("regexp-ext-rewrite-debug")
                      << "...can skip " << rc << " from " << xc << std::endl;
                }
              }
            }
          }
        }
        if (!do_next)
        {
          Trace("regexp-ext-rewrite")
              << "Cannot consume : " << xc << " " << rc << std::endl;
        }
      }
    }
    if (dir != 0)
    {
      std::reverse(children.begin(), children.end());
      std::reverse(mchildren.begin(), mchildren.end());
    }
  }
  return Node::null();
}

bool RegExpEntail::isConstRegExp(TNode t)
{
  if (t.getKind() == STRING_TO_REGEXP)
  {
    return t[0].isConst();
  }
  else if (t.isVar())
  {
    return false;
  }
  for (unsigned i = 0; i < t.getNumChildren(); ++i)
  {
    if (!isConstRegExp(t[i]))
    {
      return false;
    }
  }
  return true;
}

bool RegExpEntail::testConstStringInRegExp(CVC4::String& s,
                                                unsigned int index_start,
                                                TNode r)
{
  Assert(index_start <= s.size());
  Trace("regexp-debug") << "Checking " << s << " in " << r << ", starting at "
                        << index_start << std::endl;
  Assert(!r.isVar());
  Kind k = r.getKind();
  switch (k)
  {
    case STRING_TO_REGEXP:
    {
      CVC4::String s2 = s.substr(index_start, s.size() - index_start);
      if (r[0].isConst())
      {
        return (s2 == r[0].getConst<String>());
      }
      Assert(false) << "RegExp contains variables";
      return false;
    }
    case REGEXP_CONCAT:
    {
      if (s.size() != index_start)
      {
        std::vector<int> vec_k(r.getNumChildren(), -1);
        int start = 0;
        int left = (int)s.size() - index_start;
        int i = 0;
        while (i < (int)r.getNumChildren())
        {
          bool flag = true;
          if (i == (int)r.getNumChildren() - 1)
          {
            if (testConstStringInRegExp(s, index_start + start, r[i]))
            {
              return true;
            }
          }
          else if (i == -1)
          {
            return false;
          }
          else
          {
            for (vec_k[i] = vec_k[i] + 1; vec_k[i] <= left; ++vec_k[i])
            {
              CVC4::String t = s.substr(index_start + start, vec_k[i]);
              if (testConstStringInRegExp(t, 0, r[i]))
              {
                start += vec_k[i];
                left -= vec_k[i];
                flag = false;
                ++i;
                vec_k[i] = -1;
                break;
              }
            }
          }

          if (flag)
          {
            --i;
            if (i >= 0)
            {
              start -= vec_k[i];
              left += vec_k[i];
            }
          }
        }
        return false;
      }
      else
      {
        for (unsigned i = 0; i < r.getNumChildren(); ++i)
        {
          if (!testConstStringInRegExp(s, index_start, r[i]))
          {
            return false;
          }
        }
        return true;
      }
    }
    case REGEXP_UNION:
    {
      for (unsigned i = 0; i < r.getNumChildren(); ++i)
      {
        if (testConstStringInRegExp(s, index_start, r[i]))
        {
          return true;
        }
      }
      return false;
    }
    case REGEXP_INTER:
    {
      for (unsigned i = 0; i < r.getNumChildren(); ++i)
      {
        if (!testConstStringInRegExp(s, index_start, r[i]))
        {
          return false;
        }
      }
      return true;
    }
    case REGEXP_STAR:
    {
      if (s.size() != index_start)
      {
        for (unsigned i = s.size() - index_start; i > 0; --i)
        {
          CVC4::String t = s.substr(index_start, i);
          if (testConstStringInRegExp(t, 0, r[0]))
          {
            if (index_start + i == s.size()
                || testConstStringInRegExp(s, index_start + i, r))
            {
              return true;
            }
          }
        }
        return false;
      }
      else
      {
        return true;
      }
    }
    case REGEXP_EMPTY: { return false;
    }
    case REGEXP_SIGMA:
    {
      if (s.size() == index_start + 1)
      {
        return true;
      }
      else
      {
        return false;
      }
    }
    case REGEXP_RANGE:
    {
      if (s.size() == index_start + 1)
      {
        unsigned a = r[0].getConst<String>().front();
        unsigned b = r[1].getConst<String>().front();
        unsigned c = s.back();
        return (a <= c && c <= b);
      }
      else
      {
        return false;
      }
    }
    case REGEXP_LOOP:
    {
      NodeManager * nm = NodeManager::currentNM();
      uint32_t l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if (s.size() == index_start)
      {
        return l == 0 ? true : testConstStringInRegExp(s, index_start, r[0]);
      }
      else if (l == 0 && r[1] == r[2])
      {
        return false;
      }
      else
      {
        Assert(r.getNumChildren() == 3)
            << "String rewriter error: LOOP has 2 children";
        if (l == 0)
        {
          // R{0,u}
          uint32_t u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          for (unsigned len = s.size() - index_start; len >= 1; len--)
          {
            CVC4::String t = s.substr(index_start, len);
            if (testConstStringInRegExp(t, 0, r[0]))
            {
              if (len + index_start == s.size())
              {
                return true;
              }
              else
              {
                Node num2 =
                    nm->mkConst(CVC4::Rational(u - 1));
                Node r2 = nm->mkNode(
                    REGEXP_LOOP, r[0], r[1], num2);
                if (testConstStringInRegExp(s, index_start + len, r2))
                {
                  return true;
                }
              }
            }
          }
          return false;
        }
        else
        {
          // R{l,l}
          Assert(r[1] == r[2])
              << "String rewriter error: LOOP nums are not equal";
          if (l > s.size() - index_start)
          {
            if (testConstStringInRegExp(s, s.size(), r[0]))
            {
              l = s.size() - index_start;
            }
            else
            {
              return false;
            }
          }
          for (unsigned len = 1; len <= s.size() - index_start; len++)
          {
            CVC4::String t = s.substr(index_start, len);
            if (testConstStringInRegExp(t, 0, r[0]))
            {
              Node num2 =
                  nm->mkConst(CVC4::Rational(l - 1));
              Node r2 = nm->mkNode(
                  REGEXP_LOOP, r[0], num2, num2);
              if (testConstStringInRegExp(s, index_start + len, r2))
              {
                return true;
              }
            }
          }
          return false;
        }
      }
    }
    case REGEXP_COMPLEMENT:
    {
      return !testConstStringInRegExp(s, index_start, r[0]);
      break;
    }
    default:
    {
      Assert(!RegExpOpr::isRegExpKind(k));
      return false;
    }
  }
}

bool RegExpEntail::hasEpsilonNode(TNode node)
{
  for (const Node& nc : node)
  {
    if (nc.getKind() == STRING_TO_REGEXP && Word::isEmpty(nc[0]))
    {
      return true;
    }
  }
  return false;
}

}
}
}
