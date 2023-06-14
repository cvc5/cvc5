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
 * Rewrite database
 */

#include "expr/nary_term_util.h"

#include "expr/attribute.h"
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
  Assert(fv.getKind() == BOUND_VARIABLE);
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

bool getListVarContext(TNode n, std::map<Node, Kind>& context)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::map<Node, Kind>::iterator itc;
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
            context[cn] = cur.getKind();
          }
          else if (itc->second != cur.getKind())
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
    case OR: nullTerm = nm->mkConst(false); break;
    case AND:
    case SEP_STAR: nullTerm = nm->mkConst(true); break;
    case ADD:
      // Note that we ignore the type. This is safe since ADD is permissive
      // for subtypes.
      nullTerm = nm->mkConstInt(Rational(0));
      break;
    case MULT:
    case NONLINEAR_MULT:
      // Note that we ignore the type. This is safe since multiplication is
      // permissive for subtypes.
      nullTerm = nm->mkConstInt(Rational(1));
      break;
    case STRING_CONCAT:
      // handles strings and sequences
      nullTerm = theory::strings::Word::mkEmptyWord(tn);
      break;
    case REGEXP_CONCAT:
      // the language containing only the empty string
      nullTerm = nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String("")));
      break;
    case REGEXP_UNION:
      // empty language
      nullTerm = nm->mkNode(REGEXP_NONE);
      break;
    case REGEXP_INTER:
      // universal language
      nullTerm = nm->mkNode(REGEXP_ALL);
      break;
    case BITVECTOR_AND:
      // it may be the case that we are an abstract type, which we guard here
      // and return the null node.
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkOnes(tn.getBitVectorSize());
      }
      break;
    case BITVECTOR_OR:
    case BITVECTOR_ADD:
    case BITVECTOR_XOR:
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkZero(tn.getBitVectorSize());
      }
      break;
    case BITVECTOR_MULT:
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkOne(tn.getBitVectorSize());
      }
      break;
    case FINITE_FIELD_ADD:
      if (tn.isFiniteField())
      {
        nullTerm = nm->mkConst(FiniteFieldValue(Integer(0), tn.getFfSize()));
      }
      break;
    case FINITE_FIELD_MULT:
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
  // assumes all variables are list variables
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
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
            Assert(sd.getKind() == SEXPR);
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

}  // namespace expr
}  // namespace cvc5::internal
