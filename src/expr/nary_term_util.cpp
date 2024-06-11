/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database
 */

#include "expr/nary_term_util.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/word.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

struct IsListTag
{
};
using IsListAttr = expr::Attribute<IsListTag, bool>;

void markListVar(TNode fv)
{
  Assert(fv.isVar());
  fv.setAttribute(IsListAttr(), true);
}

bool isListVar(TNode fv) { return fv.getAttribute(IsListAttr()); }

bool hasListVar(TNode n)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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
      if (isListVar(cur))
      {
        return true;
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

bool getListVarContext(TNode n, std::map<Node, Node>& context)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::map<Node, Node>::iterator itc;
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
      if (isListVar(cur))
      {
        // top-level list variable, undefined
        return false;
      }
      for (const Node& cn : cur)
      {
        if (isListVar(cn))
        {
          itc = context.find(cn);
          if (itc == context.end())
          {
            context[cn] = cur;
          }
          else if (itc->second.getKind() != cur.getKind())
          {
            return false;
          }
          continue;
        }
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return true;
}

Node getNullTerminator(Kind k, TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nullTerm;
  switch (k)
  {
    case Kind::OR: nullTerm = nm->mkConst(false); break;
    case Kind::AND:
    case Kind::SEP_STAR: nullTerm = nm->mkConst(true); break;
    case Kind::ADD:
      // Note that we ignore the type. This is safe since ADD is permissive
      // for subtypes.
      nullTerm = nm->mkConstInt(Rational(0));
      break;
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
      // Note that we ignore the type. This is safe since multiplication is
      // permissive for subtypes.
      nullTerm = nm->mkConstInt(Rational(1));
      break;
    case Kind::STRING_CONCAT:
      // handles strings and sequences
      if (tn.isStringLike())
      {
        nullTerm = theory::strings::Word::mkEmptyWord(tn);
      }
      break;
    case Kind::REGEXP_CONCAT:
      // the language containing only the empty string
      nullTerm = nm->mkNode(Kind::STRING_TO_REGEXP, nm->mkConst(String("")));
      break;
    case Kind::REGEXP_UNION:
      // empty language
      nullTerm = nm->mkNode(Kind::REGEXP_NONE);
      break;
    case Kind::REGEXP_INTER:
      // universal language
      nullTerm = nm->mkNode(Kind::REGEXP_ALL);
      break;
    case Kind::BITVECTOR_AND:
      // it may be the case that we are an abstract type, which we guard here
      // and return the null node.
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkOnes(tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_OR:
    case Kind::BITVECTOR_ADD:
    case Kind::BITVECTOR_XOR:
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkZero(tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_MULT:
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkOne(tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_CONCAT:
    {
      nullTerm = nm->getSkolemManager()->mkSkolemFunction(SkolemId::BV_EMPTY);
    }
    break;
    case Kind::FINITE_FIELD_ADD:
      if (tn.isFiniteField())
      {
        nullTerm = nm->mkConst(FiniteFieldValue(Integer(0), tn.getFfSize()));
      }
      break;
    case Kind::FINITE_FIELD_MULT:
      if (tn.isFiniteField())
      {
        nullTerm = nm->mkConst(FiniteFieldValue(Integer(1), tn.getFfSize()));
      }
      break;
    default:
      // not handled as null-terminated
      break;
  }
  return nullTerm;
}

Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs)
{
  std::unordered_map<TNode, Node> visited;
  return narySubstitute(src, vars, subs, visited);
}

Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    std::unordered_map<TNode, Node>& visited)
{
  // assumes all variables are list variables
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  std::vector<Node>::const_iterator itv;
  TNode cur;
  visit.push_back(src);
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (!expr::hasBoundVar(cur))
      {
        visited[cur] = cur;
        visit.pop_back();
        continue;
      }
      // if it is a non-list variable, do the replacement
      itv = std::find(vars.begin(), vars.end(), cur);
      if (itv != vars.end())
      {
        size_t d = std::distance(vars.begin(), itv);
        if (!isListVar(vars[d]))
        {
          visited[cur] = subs[d];
          continue;
        }
      }
      visited[cur] = Node::null();
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        // if it is a list variable, insert the corresponding list as children;
        itv = std::find(vars.begin(), vars.end(), cn);
        if (itv != vars.end())
        {
          childChanged = true;
          size_t d = std::distance(vars.begin(), itv);
          Assert(d < subs.size());
          Node sd = subs[d];
          if (isListVar(vars[d]))
          {
            Assert(sd.getKind() == Kind::SEXPR);
            // add its children
            children.insert(children.end(), sd.begin(), sd.end());
          }
          else
          {
            children.push_back(sd);
          }
          continue;
        }
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        if (children.size() != cur.getNumChildren())
        {
          // n-ary operators cannot be parameterized
          Assert(cur.getMetaKind() != metakind::PARAMETERIZED);
          if (children.empty())
          {
            ret = getNullTerminator(cur.getKind(), cur.getType());
            // if we don't know the null terminator, just return null now
            if (ret.isNull())
            {
              return ret;
            }
          }
          else
          {
            ret = (children.size() == 1 ? children[0]
                                        : nm->mkNode(cur.getKind(), children));
          }
        }
        else
        {
          if (cur.getMetaKind() == metakind::PARAMETERIZED)
          {
            children.insert(children.begin(), cur.getOperator());
          }
          ret = nm->mkNode(cur.getKind(), children);
        }
      }
      visited[cur] = ret;
    }

  } while (!visit.empty());
  Assert(visited.find(src) != visited.end());
  Assert(!visited.find(src)->second.isNull());
  return visited[src];
}

bool isAssocCommIdem(Kind k)
{
  switch (k)
  {
    case Kind::OR:
    case Kind::AND:
    case Kind::SEP_STAR:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_INTER:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR:
    case Kind::FINITE_FIELD_ADD:
    case Kind::FINITE_FIELD_MULT: return true;
    default: break;
  }
  return false;
}

bool isAssoc(Kind k)
{
  switch (k)
  {
    case Kind::STRING_CONCAT:
    case Kind::REGEXP_CONCAT: return true;
    default: break;
  }
  // also return true for the operators listed above
  return isAssocCommIdem(k);
}

struct NormalFormTag
{
};
using NormalFormAttr = expr::Attribute<NormalFormTag, Node>;

Node getACINormalForm(Node a)
{
  NormalFormAttr nfa;
  Node an = a.getAttribute(nfa);
  if (!an.isNull())
  {
    // already computed
    return an;
  }
  Kind k = a.getKind();
  bool aci = isAssocCommIdem(k);
  if (!aci && !isAssoc(k))
  {
    // not associative, return self
    a.setAttribute(nfa, a);
    return a;
  }
  TypeNode atn = a.getType();
  Node nt = getNullTerminator(k, atn);
  if (nt.isNull())
  {
    // no null terminator, likely abstract type, return self
    a.setAttribute(nfa, a);
    return a;
  }
  std::vector<Node> toProcess;
  toProcess.insert(toProcess.end(), a.rbegin(), a.rend());
  std::vector<Node> children;
  Node cur;
  do
  {
    cur = toProcess.back();
    toProcess.pop_back();
    if (cur == nt)
    {
      // ignore null terminator (which is the neutral element)
      continue;
    }
    else if (cur.getKind() == k)
    {
      // flatten
      toProcess.insert(toProcess.end(), cur.rbegin(), cur.rend());
    }
    else if (!aci
             || std::find(children.begin(), children.end(), cur)
                    == children.end())
    {
      // add to final children if not idempotent or if not a duplicate
      children.push_back(cur);
    }
  } while (!toProcess.empty());
  if (aci)
  {
    // sort if commutative
    std::sort(children.begin(), children.end());
  }
  an = children.empty() ? nt
                        : (children.size() == 1
                               ? children[0]
                               : NodeManager::currentNM()->mkNode(k, children));
  a.setAttribute(nfa, an);
  return an;
}

bool isACINorm(Node a, Node b)
{
  Node an = getACINormalForm(a);
  Node bn = getACINormalForm(b);
  if (a.getKind() == b.getKind())
  {
    // if the kinds are equal, we compare their normal forms only, as the checks
    // below are spurious.
    return (an == bn);
  }
  // note we compare three possibilities, to handle cases like
  //   (or (and A B) false) == (and A B).
  //
  // Note that we do *not* succeed if an==bn here, since this depends on the
  // chosen ordering. For example, if (or (and A B) false) == (and B A),
  // we get a normal form of (and A B) for the LHS. The normal form of the
  // RHS is either (and A B) or (and B A). If we succeeded when an==bn,
  // then this would only be the case if the former was chosen as a normal
  // form. Instead, both fail.
  return (a == bn) || (an == b);
}

}  // namespace expr
}  // namespace cvc5::internal
