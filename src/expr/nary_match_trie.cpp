/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements a n-ary match trie
 */

#include "expr/nary_match_trie.h"

#include <sstream>
#include "expr/nary_term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

class NaryMatchFrame
{
 public:
  NaryMatchFrame(const std::vector<Node>& syms, const NaryMatchTrie* t)
      : d_syms(syms), d_trie(t), d_index(0), d_variant(0), d_boundVar(false)
  {
  }
  /** Symbols to match */
  std::vector<Node> d_syms;
  /** The match trie */
  const NaryMatchTrie* d_trie;
  /** The index we are considering, 0 = operator, n>0 = variable # (n-1) */
  size_t d_index;
  /** List length considering */
  size_t d_variant;
  /** Whether we just bound a variable */
  bool d_boundVar;
};

bool NaryMatchTrie::getMatches(Node n, NotifyMatch* ntm) const
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> vars;
  std::vector<Node> subs;
  std::map<Node, Node> smap;

  std::map<Node, NaryMatchTrie>::const_iterator itc;

  std::vector<NaryMatchFrame> visit;
  visit.push_back(NaryMatchFrame({n}, this));

  while (!visit.empty())
  {
    NaryMatchFrame& curr = visit.back();
    // currently, copy the symbols from previous frame TODO: improve?
    std::vector<Node> syms = curr.d_syms;
    const NaryMatchTrie* mt = curr.d_trie;
    if (syms.empty())
    {
      // if we matched, there must be a data member at this node
      Assert(!mt->d_data.isNull());
      // notify match?
      Assert(n == expr::narySubstitute(mt->d_data, vars, subs));
      Trace("match-debug") << "notify : " << mt->d_data << std::endl;
      if (!ntm->notify(n, mt->d_data, vars, subs))
      {
        return false;
      }
      visit.pop_back();
      continue;
    }

    // clean up if we previously bound a variable
    if (curr.d_boundVar)
    {
      Assert(!vars.empty());
      Assert(smap.find(vars.back()) != smap.end());
      smap.erase(vars.back());
      vars.pop_back();
      subs.pop_back();
      curr.d_boundVar = false;
    }

    if (curr.d_index == 0)
    {
      curr.d_index++;
      // finished matching variables, try to match the operator
      Node next = syms.back();
      Node op =
          (!next.isNull() && next.hasOperator()) ? next.getOperator() : next;
      itc = mt->d_children.find(op);
      if (itc != mt->d_children.end())
      {
        syms.pop_back();
        // push the children + null termination marker, in reverse order
        if (NodeManager::isNAryKind(next.getKind()))
        {
          syms.push_back(Node::null());
        }
        if (next.hasOperator())
        {
          syms.insert(syms.end(), next.rbegin(), next.rend());
        }
        // new frame
        visit.push_back(NaryMatchFrame(syms, &itc->second));
      }
    }
    else if (curr.d_index <= mt->d_vars.size())
    {
      // try to match the next (variable, length)
      Node var;
      Node next;
      do
      {
        var = mt->d_vars[curr.d_index - 1];
        Assert(mt->d_children.find(var) != mt->d_children.end());
        std::vector<Node> currChildren;
        if (isListVar(var))
        {
          // get the length of the list we want to consider
          size_t l = curr.d_variant;
          curr.d_variant++;
          // match with l, or increment d_index otherwise
          bool foundChildren = true;
          // We are in a state where the children of an n-ary child
          // have been pused to syms. We try to extract l children here. If
          // we encounter the null symbol, then we do not have sufficient
          // children to match for this variant and fail.
          for (size_t i = 0; i < l; i++)
          {
            Assert(!syms.empty());
            Node s = syms.back();
            // we currently reject the term if it does not have the same
            // type as the list variable. This rejects certain corner cases of
            // arithmetic operators which are permissive for subtyping.
            // For example, if x is a list variable of type Real, y is a list
            // variable of type Real, then (+ x y) does *not* match
            // (+ 1.0 2 1.5), despite { x -> (+ 1.0 2), y -> 1.5 } being
            // a well-typed match.
            if (s.isNull() || !s.getType().isComparableTo(var.getType()))
            {
              foundChildren = false;
              break;
            }
            currChildren.push_back(s);
            syms.pop_back();
          }
          if (foundChildren)
          {
            // we are matching the next list
            next = nm->mkNode(SEXPR, currChildren);
          }
          else
          {
            // otherwise, we have run out of variants, go to next variable
            curr.d_index++;
            curr.d_variant = 0;
          }
        }
        else
        {
          next = syms.back();
          curr.d_index++;
          // we could be at the end of an n-ary operator, in which case we
          // do not match
          if (!next.isNull())
          {
            currChildren.push_back(next);
            syms.pop_back();
            Trace("match-debug")
                << "Compare types " << var << " " << next << " "
                << var.getType() << " " << next.getType() << std::endl;
            // check types in the (non-list) case
            if (!var.getType().isComparableTo(next.getType()))
            {
              Trace("match-debug") << "...fail" << std::endl;
              next = Node::null();
            }
          }
        }
        if (!next.isNull())
        {
          // check if it is already bound, do the binding if necessary
          std::map<Node, Node>::iterator its = smap.find(var);
          if (its != smap.end())
          {
            if (its->second != next)
            {
              // failed to match
              next = Node::null();
            }
            // otherwise, successfully matched, nothing to do
          }
          else
          {
            // add to binding
            Trace("match-debug")
                << "Set " << var << " -> " << next << std::endl;
            vars.push_back(var);
            subs.push_back(next);
            smap[var] = next;
            curr.d_boundVar = true;
          }
        }
        if (next.isNull())
        {
          // if we failed, revert changes to syms
          syms.insert(syms.end(), currChildren.rbegin(), currChildren.rend());
        }
      } while (next.isNull() && curr.d_index <= mt->d_vars.size());
      if (next.isNull())
      {
        // we are out of variables to match, finished with this frame
        visit.pop_back();
        continue;
      }
      Trace("match-debug") << "recurse var : " << var << std::endl;
      itc = mt->d_children.find(var);
      Assert(itc != mt->d_children.end());
      visit.push_back(NaryMatchFrame(syms, &itc->second));
    }
    else
    {
      // no variables to match, we are done
      visit.pop_back();
    }
  }
  return true;
}

void NaryMatchTrie::addTerm(Node n)
{
  Assert(!n.isNull());
  std::vector<Node> visit;
  visit.push_back(n);
  NaryMatchTrie* curr = this;
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    if (cn.isNull())
    {
      curr = &(curr->d_children[cn]);
    }
    else if (cn.hasOperator())
    {
      curr = &(curr->d_children[cn.getOperator()]);
      // add null terminator if an n-ary kind
      if (NodeManager::isNAryKind(cn.getKind()))
      {
        visit.push_back(Node::null());
      }
      // note children are processed left to right
      visit.insert(visit.end(), cn.rbegin(), cn.rend());
    }
    else
    {
      if (cn.isVar()
          && std::find(curr->d_vars.begin(), curr->d_vars.end(), cn)
                 == curr->d_vars.end())
      {
        curr->d_vars.push_back(cn);
      }
      curr = &(curr->d_children[cn]);
    }
  }
  curr->d_data = n;
}

void NaryMatchTrie::clear()
{
  d_children.clear();
  d_vars.clear();
  d_data = Node::null();
}

std::string NaryMatchTrie::debugPrint() const
{
  std::stringstream ss;
  std::vector<std::tuple<const NaryMatchTrie*, size_t, Node>> visit;
  visit.emplace_back(this, 0, Node::null());
  do
  {
    std::tuple<const NaryMatchTrie*, size_t, Node> curr = visit.back();
    visit.pop_back();
    size_t indent = std::get<1>(curr);
    for (size_t i = 0; i < indent; i++)
    {
      ss << "  ";
    }
    Node n = std::get<2>(curr);
    if (indent == 0)
    {
      ss << ".";
    }
    else
    {
      ss << n;
    }
    ss << ((!n.isNull() && isListVar(n)) ? " [*]" : "");
    ss << std::endl;
    const NaryMatchTrie* mt = std::get<0>(curr);
    for (const std::pair<const Node, NaryMatchTrie>& c : mt->d_children)
    {
      visit.emplace_back(&c.second, indent + 1, c.first);
    }
  } while (!visit.empty());
  return ss.str();
}

}  // namespace expr
}  // namespace cvc5::internal
