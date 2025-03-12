/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of entailment tests involving regular expressions.
 */

#include "theory/strings/regexp_entail.h"

#include "theory/rewriter.h"
#include "theory/strings/regexp_eval.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/string.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

RegExpEntail::RegExpEntail(NodeManager* nm, Rewriter* r) : d_aent(nm, r)
{
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
}

Node RegExpEntail::simpleRegexpConsume(NodeManager* nm,
                                       std::vector<Node>& mchildren,
                                       std::vector<Node>& children,
                                       int dir)
{
  Trace("regexp-ext-rewrite-debug")
      << "Simple reg exp consume, dir=" << dir << ":" << std::endl;
  unsigned tmin = dir < 0 ? 0 : dir;
  unsigned tmax = dir < 0 ? 1 : dir;
  // try to remove off front and back
  for (unsigned t = 0; t < 2; t++)
  {
    if (tmin <= t && t <= tmax)
    {
      Trace("regexp-ext-rewrite-debug")
          << "Run consume, direction is " << t << " with:" << std::endl;
      Trace("regexp-ext-rewrite-debug")
          << "  mchildren : " << mchildren << std::endl;
      Trace("regexp-ext-rewrite-debug")
          << "  children : " << children << std::endl;
      bool do_next = true;
      while (!children.empty() && !mchildren.empty() && do_next)
      {
        do_next = false;
        Node xc = mchildren[mchildren.size() - 1];
        Node rc = children[children.size() - 1];
        Trace("regexp-ext-rewrite-debug")
            << "* " << xc << " in " << rc << std::endl;
        Assert(rc.getKind() != Kind::REGEXP_CONCAT);
        Assert(xc.getKind() != Kind::STRING_CONCAT);
        if (rc.getKind() == Kind::STRING_TO_REGEXP)
        {
          std::vector<Node> childrenc;
          utils::getConcat(rc[0], childrenc);
          size_t cindex = t == 1 ? 0 : childrenc.size() - 1;
          Node rcc = childrenc[cindex];
          Node remStr;
          if (xc == rcc)
          {
            mchildren.pop_back();
            do_next = true;
            Trace("regexp-ext-rewrite-debug") << "- strip equal" << std::endl;
          }
          else if (rcc.isConst() && Word::isEmpty(rcc))
          {
            Trace("regexp-ext-rewrite-debug")
                << "- ignore empty RE" << std::endl;
            // ignore and continue
            do_next = true;
          }
          else if (xc.isConst() && rcc.isConst())
          {
            // split the constant
            size_t index;
            remStr = Word::splitConstant(xc, rcc, index, t == 0);
            Trace("regexp-ext-rewrite-debug")
                << "- CRE: Regexp const split : " << xc << " " << rcc << " -> "
                << remStr << " " << index << " " << t << std::endl;
            if (remStr.isNull())
            {
              Trace("regexp-ext-rewrite-debug")
                  << "...return false" << std::endl;
              return nm->mkConst(false);
            }
            else
            {
              Trace("regexp-ext-rewrite-debug")
                  << "- strip equal const" << std::endl;
              mchildren.pop_back();
              if (index == 0)
              {
                mchildren.push_back(remStr);
                // we've processed the remainder as leftover for the LHS
                // string, clear it now
                remStr = Node::null();
              }
              // otherwise remStr is processed below
            }
            Trace("regexp-ext-rewrite-debug") << "- split const" << std::endl;
            do_next = true;
          }
          if (do_next)
          {
            if (remStr.isNull())
            {
              // we have fully processed the component
              childrenc.erase(childrenc.begin() + cindex);
            }
            else
            {
              // we have a remainder
              childrenc[cindex] = remStr;
            }
            if (childrenc.empty())
            {
              // if childrenc is empty, we are done with the current str.to_re
              children.pop_back();
            }
            else
            {
              // otherwise we reconstruct it
              TypeNode stype = nm->stringType();
              children[children.size() - 1] = nm->mkNode(
                  Kind::STRING_TO_REGEXP, utils::mkConcat(childrenc, stype));
            }
          }
        }
        else if (xc.isConst())
        {
          // check for constants
          cvc5::internal::String s = xc.getConst<String>();
          if (Word::isEmpty(xc))
          {
            Trace("regexp-ext-rewrite-debug") << "- ignore empty" << std::endl;
            // ignore and continue
            mchildren.pop_back();
            do_next = true;
          }
          else if (rc.getKind() == Kind::REGEXP_RANGE
                   || rc.getKind() == Kind::REGEXP_ALLCHAR)
          {
            if (!isConstRegExp(rc))
            {
              // if a non-standard re.range term, abort
              break;
            }
            std::vector<unsigned> ssVec;
            ssVec.push_back(t == 0 ? s.back() : s.front());
            cvc5::internal::String ss(ssVec);
            if (testConstStringInRegExp(ss, rc))
            {
              // strip off one character
              mchildren.pop_back();
              if (s.size() > 1)
              {
                if (t == 0)
                {
                  mchildren.push_back(nm->mkConst(s.substr(0, s.size() - 1)));
                }
                else
                {
                  mchildren.push_back(nm->mkConst(s.substr(1)));
                }
              }
              children.pop_back();
              do_next = true;
            }
            else
            {
              Trace("regexp-ext-rewrite-debug")
                  << "...return false" << std::endl;
              return nm->mkConst(false);
            }
          }
          else if (rc.getKind() == Kind::REGEXP_INTER
                   || rc.getKind() == Kind::REGEXP_UNION)
          {
            // see if any/each child does not work
            bool result_valid = true;
            Node result;
            Node emp_s = nm->mkConst(String(""));
            for (unsigned i = 0; i < rc.getNumChildren(); i++)
            {
              std::vector<Node> mchildren_s;
              std::vector<Node> children_s;
              mchildren_s.push_back(xc);
              utils::getConcat(rc[i], children_s);
              Trace("regexp-ext-rewrite-debug") << push;
              Node ret = simpleRegexpConsume(nm, mchildren_s, children_s, t);
              Trace("regexp-ext-rewrite-debug") << pop;
              if (!ret.isNull())
              {
                // one conjunct cannot be satisfied, return false
                if (rc.getKind() == Kind::REGEXP_INTER)
                {
                  Trace("regexp-ext-rewrite-debug")
                      << "...return " << ret << std::endl;
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
                Assert(rc.getKind() == Kind::REGEXP_UNION);
                Trace("regexp-ext-rewrite-debug")
                    << "...return false" << std::endl;
                return nm->mkConst(false);
              }
              else
              {
                Trace("regexp-ext-rewrite-debug")
                    << "- same result, try again, children now " << children
                    << std::endl;
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
          else if (rc.getKind() == Kind::REGEXP_STAR)
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
                << "- recursive call on body of star" << std::endl;
            Trace("regexp-ext-rewrite-debug") << push;
            Node ret = simpleRegexpConsume(nm, mchildren_s, children_s, t);
            Trace("regexp-ext-rewrite-debug") << pop;
            if (!ret.isNull())
            {
              Trace("regexp-ext-rewrite-debug")
                  << "- CRE : regexp star infeasable " << xc << " " << rc
                  << std::endl;
              children.pop_back();
              if (!children.empty())
              {
                Trace("regexp-ext-rewrite-debug") << "- continue" << std::endl;
                do_next = true;
              }
            }
            else
            {
              if (children_s.empty())
              {
                // Check if beyond this, we hit a conflict. In this case, we
                // must repeat.  Notice that we do not treat the case where
                // there are no more strings to consume as a failure, since
                // we may be within a recursive call, see issue #5510.
                bool can_skip = true;
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
                  Trace("regexp-ext-rewrite-debug")
                      << "- recursive call required repeat star" << std::endl;
                  Trace("regexp-ext-rewrite-debug") << push;
                  Node rets =
                      simpleRegexpConsume(nm, mchildren_ss, children_ss, t);
                  Trace("regexp-ext-rewrite-debug") << pop;
                  if (!rets.isNull())
                  {
                    can_skip = false;
                  }
                }
                if (!can_skip)
                {
                  TypeNode stype = nm->stringType();
                  Node prev = utils::mkConcat(mchildren, stype);
                  Trace("regexp-ext-rewrite-debug")
                      << "- can't skip" << std::endl;
                  // take the result of fully consuming once
                  if (t == 1)
                  {
                    std::reverse(mchildren_s.begin(), mchildren_s.end());
                  }
                  mchildren.clear();
                  mchildren.insert(
                      mchildren.end(), mchildren_s.begin(), mchildren_s.end());
                  Node curr = utils::mkConcat(mchildren, stype);
                  do_next = (prev != curr);
                  Trace("regexp-ext-rewrite-debug")
                      << "- do_next = " << do_next << std::endl;
                }
                else
                {
                  Trace("regexp-ext-rewrite-debug")
                      << "- can skip " << rc << " from " << xc << std::endl;
                }
              }
            }
          }
        }
        if (!do_next)
        {
          Trace("regexp-ext-rewrite")
              << "- cannot consume : " << xc << " " << rc << std::endl;
        }
      }
    }
    if (dir != 0)
    {
      std::reverse(children.begin(), children.end());
      std::reverse(mchildren.begin(), mchildren.end());
    }
  }
  Trace("regexp-ext-rewrite-debug") << "...finished, return null" << std::endl;
  return Node::null();
}

bool RegExpEntail::isConstRegExp(TNode t)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Kind ck = cur.getKind();
      if (ck == Kind::STRING_TO_REGEXP)
      {
        if (!cur[0].isConst())
        {
          return false;
        }
      }
      else if (ck == Kind::REGEXP_RV)
      {
        return false;
      }
      else if (ck == Kind::REGEXP_RANGE)
      {
        if (!utils::isCharacterRange(cur))
        {
          return false;
        }
      }
      else if (!utils::isRegExpKind(ck))
      {
        return false;
      }
      else
      {
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
  } while (!visit.empty());
  return true;
}

bool RegExpEntail::testConstStringInRegExp(String& s, TNode r)
{
  Kind k = r.getKind();
  if (k == Kind::REGEXP_CONCAT || k == Kind::REGEXP_STAR
      || k == Kind::REGEXP_UNION)
  {
    // If we can evaluate it via NFA construction, do so. We only do this
    // for compound regular expressions (re.++, re.*, re.union) which may
    // have non-trivial NFA constructions, otherwise the check below will
    // be simpler.
    if (RegExpEval::canEvaluate(r))
    {
      return RegExpEval::evaluate(s, r);
    }
  }
  return testConstStringInRegExpInternal(s, 0, r);
}

bool RegExpEntail::testConstStringInRegExpInternal(String& s,
                                                   unsigned index_start,
                                                   TNode r)
{
  Assert(index_start <= s.size());
  Trace("regexp-debug") << "Checking " << s << " in " << r << ", starting at "
                        << index_start << std::endl;
  Assert(!r.isVar());
  Kind k = r.getKind();
  switch (k)
  {
    case Kind::STRING_TO_REGEXP:
    {
      String s2 = s.substr(index_start, s.size() - index_start);
      if (r[0].isConst())
      {
        return (s2 == r[0].getConst<String>());
      }
      Assert(false) << "RegExp contains variables";
      return false;
    }
    case Kind::REGEXP_CONCAT:
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
            if (testConstStringInRegExpInternal(s, index_start + start, r[i]))
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
              cvc5::internal::String t = s.substr(index_start + start, vec_k[i]);
              if (testConstStringInRegExpInternal(t, 0, r[i]))
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
          if (!testConstStringInRegExpInternal(s, index_start, r[i]))
          {
            return false;
          }
        }
        return true;
      }
    }
    case Kind::REGEXP_UNION:
    {
      for (unsigned i = 0; i < r.getNumChildren(); ++i)
      {
        if (testConstStringInRegExpInternal(s, index_start, r[i]))
        {
          return true;
        }
      }
      return false;
    }
    case Kind::REGEXP_INTER:
    {
      for (unsigned i = 0; i < r.getNumChildren(); ++i)
      {
        if (!testConstStringInRegExpInternal(s, index_start, r[i]))
        {
          return false;
        }
      }
      return true;
    }
    case Kind::REGEXP_STAR:
    {
      if (s.size() != index_start)
      {
        for (unsigned i = s.size() - index_start; i > 0; --i)
        {
          cvc5::internal::String t = s.substr(index_start, i);
          if (testConstStringInRegExpInternal(t, 0, r[0]))
          {
            if (index_start + i == s.size()
                || testConstStringInRegExpInternal(s, index_start + i, r))
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
    case Kind::REGEXP_NONE:
    {
      return false;
    }
    case Kind::REGEXP_ALLCHAR:
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
    case Kind::REGEXP_RANGE:
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
    case Kind::REGEXP_LOOP:
    {
      NodeManager* nm = r.getNodeManager();
      uint32_t l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if (s.size() == index_start)
      {
        return l == 0 || testConstStringInRegExpInternal(s, index_start, r[0]);
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
            cvc5::internal::String t = s.substr(index_start, len);
            if (testConstStringInRegExpInternal(t, 0, r[0]))
            {
              if (len + index_start == s.size())
              {
                return true;
              }
              else
              {
                Node num2 = nm->mkConstInt(cvc5::internal::Rational(u - 1));
                Node r2 = nm->mkNode(Kind::REGEXP_LOOP, r[0], r[1], num2);
                if (testConstStringInRegExpInternal(s, index_start + len, r2))
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
            if (testConstStringInRegExpInternal(s, s.size(), r[0]))
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
            cvc5::internal::String t = s.substr(index_start, len);
            if (testConstStringInRegExpInternal(t, 0, r[0]))
            {
              Node num2 = nm->mkConstInt(cvc5::internal::Rational(l - 1));
              Node r2 = nm->mkNode(Kind::REGEXP_LOOP, r[0], num2, num2);
              if (testConstStringInRegExpInternal(s, index_start + len, r2))
              {
                return true;
              }
            }
          }
          return false;
        }
      }
    }
    case Kind::REGEXP_COMPLEMENT:
    {
      return !testConstStringInRegExpInternal(s, index_start, r[0]);
      break;
    }
    default:
    {
      Assert(!utils::isRegExpKind(k));
      return false;
    }
  }
}

bool RegExpEntail::hasEpsilonNode(TNode node)
{
  for (const Node& nc : node)
  {
    if (nc.getKind() == Kind::STRING_TO_REGEXP && Word::isEmpty(nc[0]))
    {
      return true;
    }
  }
  return false;
}

Node RegExpEntail::getFixedLengthForRegexp(TNode n)
{
  NodeManager* nm = n.getNodeManager();
  Kind k = n.getKind();
  if (k == Kind::STRING_TO_REGEXP)
  {
    if (n[0].isConst())
    {
      return nm->mkConstInt(Rational(Word::getLength(n[0])));
    }
  }
  else if (k == Kind::REGEXP_ALLCHAR || k == Kind::REGEXP_RANGE)
  {
    return nm->mkConstInt(Rational(1));
  }
  else if (k == Kind::REGEXP_UNION || k == Kind::REGEXP_INTER)
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
  else if (k == Kind::REGEXP_CONCAT)
  {
    Rational sum(0);
    for (const Node& nc : n)
    {
      Node flc = getFixedLengthForRegexp(nc);
      if (flc.isNull())
      {
        return flc;
      }
      Assert(flc.isConst() && flc.getType().isInteger());
      sum += flc.getConst<Rational>();
    }
    return nm->mkConstInt(sum);
  }
  return Node::null();
}

Node RegExpEntail::getConstantBoundLengthForRegexp(TNode n, bool isLower) const
{
  Assert(n.getType().isRegExp());
  Node ret;
  if (getConstantBoundCache(n, isLower, ret))
  {
    return ret;
  }
  Kind k = n.getKind();
  NodeManager* nm = n.getNodeManager();
  if (k == Kind::STRING_TO_REGEXP)
  {
    ret = d_aent.getConstantBoundLength(n[0], isLower);
  }
  else if (k == Kind::REGEXP_ALLCHAR || k == Kind::REGEXP_RANGE)
  {
    ret = d_one;
  }
  else if (k == Kind::REGEXP_UNION || k == Kind::REGEXP_INTER
           || k == Kind::REGEXP_CONCAT)
  {
    bool success = true;
    bool firstTime = true;
    Rational rr(0);
    for (const Node& nc : n)
    {
      Node bc = getConstantBoundLengthForRegexp(nc, isLower);
      if (bc.isNull())
      {
        if (k == Kind::REGEXP_UNION || (k == Kind::REGEXP_CONCAT && !isLower))
        {
          // since the bound could not be determined on the component, the
          // overall bound is undetermined.
          success = false;
          break;
        }
        else
        {
          // if intersection, or we are computing lower bound for concat
          // and the component cannot be determined, ignore it
          continue;
        }
      }
      Assert(bc.isConst() && bc.getType().isInteger());
      Rational r = bc.getConst<Rational>();
      if (k == Kind::REGEXP_CONCAT)
      {
        rr += r;
      }
      else if (firstTime)
      {
        rr = r;
      }
      else if ((k == Kind::REGEXP_UNION) == isLower)
      {
        rr = std::min(r, rr);
      }
      else
      {
        rr = std::max(r, rr);
      }
      firstTime = false;
    }
    // if we were successful and didn't ignore all components
    if (success && !firstTime)
    {
      ret = nm->mkConstInt(rr);
    }
  }
  if (ret.isNull() && isLower)
  {
    ret = d_zero;
  }
  Trace("strings-rentail") << "getConstantBoundLengthForRegexp: " << n
                           << ", isLower=" << isLower << " returns " << ret
                           << std::endl;
  setConstantBoundCache(n, ret, isLower);
  return ret;
}

bool RegExpEntail::regExpIncludes(Node r1,
                                  Node r2,
                                  std::map<std::pair<Node, Node>, bool>& cache)
{
  if (r1 == r2)
  {
    return true;
  }
  std::pair<Node, Node> key = std::make_pair(r1, r2);
  const auto& it = cache.find(key);
  if (it != cache.end())
  {
    return (*it).second;
  }
  // first, check some basic inclusions
  bool ret = false;
  Kind k2 = r2.getKind();
  // if the right hand side is a constant string, this is a membership test
  if (k2 == Kind::STRING_TO_REGEXP)
  {
    // only check if r1 is a constant regular expression
    if (r2[0].isConst() && isConstRegExp(r1))
    {
      String s = r2[0].getConst<String>();
      ret = testConstStringInRegExp(s, r1);
    }
    cache[key] = ret;
    return ret;
  }
  Kind k1 = r1.getKind();
  bool retSet = false;
  if (k1 == Kind::REGEXP_UNION)
  {
    retSet = true;
    // if any component of r1 includes r2, return true
    for (const Node& r : r1)
    {
      if (regExpIncludes(r, r2, cache))
      {
        ret = true;
        break;
      }
    }
  }
  if (k2 == Kind::REGEXP_INTER && !ret)
  {
    retSet = true;
    // if r1 includes any component of r2, return true
    for (const Node& r : r2)
    {
      if (regExpIncludes(r1, r, cache))
      {
        ret = true;
        break;
      }
    }
  }
  if (k1 == Kind::REGEXP_STAR)
  {
    retSet = true;
    // inclusion if r1 is (re.* re.allchar), or if the body of r1 includes r2
    // (or the body of r2 if it is also a star).
    if (r1[0].getKind() == Kind::REGEXP_ALLCHAR)
    {
      ret = true;
    }
    else
    {
      ret = regExpIncludes(r1[0], k2 == Kind::REGEXP_STAR ? r2[0] : r2, cache);
    }
  }
  else if (k1 == Kind::STRING_TO_REGEXP)
  {
    // only way to include is if equal, which was already checked
    retSet = true;
  }
  else if (k1 == Kind::REGEXP_RANGE && utils::isCharacterRange(r1))
  {
    retSet = true;
    // if comparing subranges, we check inclusion of interval
    if (k2 == Kind::REGEXP_RANGE && utils::isCharacterRange(r2))
    {
      unsigned l1 = r1[0].getConst<String>().front();
      unsigned u1 = r1[1].getConst<String>().front();
      unsigned l2 = r2[0].getConst<String>().front();
      unsigned u2 = r2[1].getConst<String>().front();
      ret = l1 <= l2 && l2 <= u1 && l1 <= u2 && u2 <= u1;
    }
  }
  if (retSet)
  {
    cache[key] = ret;
    return ret;
  }
  // avoid infinite loop
  cache[key] = false;
  NodeManager* nm = r1.getNodeManager();
  Node sigma = nm->mkNode(Kind::REGEXP_ALLCHAR, std::vector<Node>{});
  Node sigmaStar = nm->mkNode(Kind::REGEXP_STAR, sigma);

  std::vector<Node> v1, v2;
  utils::getRegexpComponents(r1, v1);
  utils::getRegexpComponents(r2, v2);

  // In the following, we iterate over `r2` (the "includee") and try to
  // match it with `r1`. `idxs`/`newIdxs` keep track of all the possible
  // positions in `r1` that we could currently be at.
  std::unordered_set<size_t> newIdxs = {0};
  std::unordered_set<size_t> idxs;
  for (const Node& n2 : v2)
  {
    // Transfer elements from `newIdxs` to `idxs`. Out-of-bound indices are
    // removed and for (re.* re.allchar), we additionally include the option of
    // skipping it. Indices must be smaller than the size of `v1`.
    idxs.clear();
    for (size_t idx : newIdxs)
    {
      if (idx < v1.size())
      {
        idxs.insert(idx);
        if (idx + 1 < v1.size() && v1[idx] == sigmaStar)
        {
          Assert(idx + 1 == v1.size() || v1[idx + 1] != sigmaStar);
          idxs.insert(idx + 1);
        }
      }
    }
    newIdxs.clear();

    for (size_t idx : idxs)
    {
      if (regExpIncludes(v1[idx], n2, cache))
      {
        // If this component includes n2, then we can consume it.
        newIdxs.insert(idx + 1);
      }
      if (v1[idx] == sigmaStar)
      {
        // (re.* re.allchar) can match an arbitrary amount of `r2`
        newIdxs.insert(idx);
      }
      else if (utils::isUnboundedWildcard(v1, idx))
      {
        // If a series of re.allchar is followed by (re.* re.allchar), we
        // can decide not to "waste" the re.allchar because the order of
        // the two wildcards is not observable (i.e. it does not change
        // the sequences matched by the regular expression)
        newIdxs.insert(idx);
      }
    }

    if (newIdxs.empty())
    {
      // If there are no candidates, we can't match the remainder of r2
      break;
    }
  }

  // We have processed all of `r2`. We are now looking if there was also a
  // path to the end in `r1`. This makes sure that we don't have leftover
  // bits in `r1` that don't match anything in `r2`.
  bool result = false;
  for (size_t idx : newIdxs)
  {
    if (idx == v1.size() || (idx == v1.size() - 1 && v1[idx] == sigmaStar))
    {
      result = true;
      break;
    }
  }
  cache[key] = result;
  return result;
}

bool RegExpEntail::regExpIncludes(Node r1, Node r2)
{
  std::map<std::pair<Node, Node>, bool> cache;
  return regExpIncludes(r1, r2, cache);
}

Node RegExpEntail::getGeneralizedConstRegExp(const Node& n)
{
  Assert(n.getType().isString());
  NodeManager* nm = n.getNodeManager();
  std::vector<Node> ncs;
  if (n.getKind() == Kind::STRING_CONCAT)
  {
    ncs.insert(ncs.end(), n.begin(), n.end());
  }
  else
  {
    ncs.push_back(n);
  }
  bool nonTrivial = false;
  Node sigmaStar =
      nm->mkNode(Kind::REGEXP_STAR, nm->mkNode(Kind::REGEXP_ALLCHAR));
  std::vector<Node> rs;
  for (const Node& nc : ncs)
  {
    Node re = sigmaStar;
    if (nc.isConst())
    {
      nonTrivial = true;
      re = nm->mkNode(Kind::STRING_TO_REGEXP, nc);
    }
    else if (nc.getKind() == Kind::STRING_ITOS)
    {
      nonTrivial = true;
      Node digRange = nm->mkNode(Kind::REGEXP_RANGE,
                                 nm->mkConst(String("0")),
                                 nm->mkConst(String("9")));
      re = nm->mkNode(Kind::REGEXP_STAR, digRange);
      // maybe non-empty digit range?
      // relies on RARE rule str-in-re-from-int-dig-range to prove
      if (d_aent.check(nc[0]))
      {
        re = nm->mkNode(Kind::REGEXP_CONCAT, digRange, re);
      }
    }
    rs.push_back(re);
  }
  if (nonTrivial)
  {
    return rs.size() == 1 ? rs[0] : nm->mkNode(Kind::REGEXP_CONCAT, rs);
  }
  return Node::null();
}

struct RegExpEntailConstantBoundLowerId
{
};
typedef expr::Attribute<RegExpEntailConstantBoundLowerId, Node>
    RegExpEntailConstantBoundLower;

struct RegExpEntailConstantBoundUpperId
{
};
typedef expr::Attribute<RegExpEntailConstantBoundUpperId, Node>
    RegExpEntailConstantBoundUpper;

void RegExpEntail::setConstantBoundCache(TNode n, Node ret, bool isLower)
{
  if (isLower)
  {
    RegExpEntailConstantBoundLower rcbl;
    n.setAttribute(rcbl, ret);
  }
  else
  {
    RegExpEntailConstantBoundUpper rcbu;
    n.setAttribute(rcbu, ret);
  }
}

bool RegExpEntail::getConstantBoundCache(TNode n, bool isLower, Node& c)
{
  if (isLower)
  {
    RegExpEntailConstantBoundLower rcbl;
    if (n.hasAttribute(rcbl))
    {
      c = n.getAttribute(rcbl);
      return true;
    }
  }
  else
  {
    RegExpEntailConstantBoundUpper rcbu;
    if (n.hasAttribute(rcbu))
    {
      c = n.getAttribute(rcbu);
      return true;
    }
  }
  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
