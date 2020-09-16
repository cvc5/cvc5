/*********************                                                        */
/*! \file match_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements a match trie, also known as a discrimination tree.
 **/

#include "expr/match_trie.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace expr {

bool MatchTrie::getMatches(Node n, NotifyMatch* ntm)
{
  std::vector<Node> vars;
  std::vector<Node> subs;
  std::map<Node, Node> smap;

  std::vector<std::vector<Node> > visit;
  std::vector<MatchTrie*> visit_trie;
  std::vector<int> visit_var_index;
  std::vector<bool> visit_bound_var;

  visit.push_back(std::vector<Node>{n});
  visit_trie.push_back(this);
  visit_var_index.push_back(-1);
  visit_bound_var.push_back(false);
  while (!visit.empty())
  {
    std::vector<Node> cvisit = visit.back();
    MatchTrie* curr = visit_trie.back();
    if (cvisit.empty())
    {
      Assert(n
             == curr->d_data.substitute(
                 vars.begin(), vars.end(), subs.begin(), subs.end()));
      Trace("match-debug") << "notify : " << curr->d_data << std::endl;
      if (!ntm->notify(n, curr->d_data, vars, subs))
      {
        return false;
      }
      visit.pop_back();
      visit_trie.pop_back();
      visit_var_index.pop_back();
      visit_bound_var.pop_back();
    }
    else
    {
      Node cn = cvisit.back();
      Trace("match-debug") << "traverse : " << cn << " at depth "
                           << visit.size() << std::endl;
      unsigned index = visit.size() - 1;
      int vindex = visit_var_index[index];
      if (vindex == -1)
      {
        if (!cn.isVar())
        {
          Node op = cn.hasOperator() ? cn.getOperator() : cn;
          unsigned nchild = cn.hasOperator() ? cn.getNumChildren() : 0;
          std::map<unsigned, MatchTrie>::iterator itu =
              curr->d_children[op].find(nchild);
          if (itu != curr->d_children[op].end())
          {
            // recurse on the operator or self
            cvisit.pop_back();
            if (cn.hasOperator())
            {
              for (const Node& cnc : cn)
              {
                cvisit.push_back(cnc);
              }
            }
            Trace("match-debug") << "recurse op : " << op << std::endl;
            visit.push_back(cvisit);
            visit_trie.push_back(&itu->second);
            visit_var_index.push_back(-1);
            visit_bound_var.push_back(false);
          }
        }
        visit_var_index[index]++;
      }
      else
      {
        // clean up if we previously bound a variable
        if (visit_bound_var[index])
        {
          Assert(!vars.empty());
          smap.erase(vars.back());
          vars.pop_back();
          subs.pop_back();
          visit_bound_var[index] = false;
        }

        if (vindex == static_cast<int>(curr->d_vars.size()))
        {
          Trace("match-debug")
              << "finished checking " << curr->d_vars.size()
              << " variables at depth " << visit.size() << std::endl;
          // finished
          visit.pop_back();
          visit_trie.pop_back();
          visit_var_index.pop_back();
          visit_bound_var.pop_back();
        }
        else
        {
          Trace("match-debug") << "check variable #" << vindex << " at depth "
                               << visit.size() << std::endl;
          Assert(vindex < static_cast<int>(curr->d_vars.size()));
          // recurse on variable?
          Node var = curr->d_vars[vindex];
          bool recurse = true;
          // check if it is already bound
          std::map<Node, Node>::iterator its = smap.find(var);
          if (its != smap.end())
          {
            if (its->second != cn)
            {
              recurse = false;
            }
          }
          else if (!var.getType().isSubtypeOf(cn.getType()))
          {
            recurse = false;
          }
          else
          {
            vars.push_back(var);
            subs.push_back(cn);
            smap[var] = cn;
            visit_bound_var[index] = true;
          }
          if (recurse)
          {
            Trace("match-debug") << "recurse var : " << var << std::endl;
            cvisit.pop_back();
            visit.push_back(cvisit);
            visit_trie.push_back(&curr->d_children[var][0]);
            visit_var_index.push_back(-1);
            visit_bound_var.push_back(false);
          }
          visit_var_index[index]++;
        }
      }
    }
  }
  return true;
}

void MatchTrie::addTerm(Node n)
{
  Assert(!n.isNull());
  std::vector<Node> visit;
  visit.push_back(n);
  MatchTrie* curr = this;
  while (!visit.empty())
  {
    Node cn = visit.back();
    visit.pop_back();
    if (cn.hasOperator())
    {
      curr = &(curr->d_children[cn.getOperator()][cn.getNumChildren()]);
      for (const Node& cnc : cn)
      {
        visit.push_back(cnc);
      }
    }
    else
    {
      if (cn.isVar()
          && std::find(curr->d_vars.begin(), curr->d_vars.end(), cn)
                 == curr->d_vars.end())
      {
        curr->d_vars.push_back(cn);
      }
      curr = &(curr->d_children[cn][0]);
    }
  }
  curr->d_data = n;
}

void MatchTrie::clear()
{
  d_children.clear();
  d_vars.clear();
  d_data = Node::null();
}

}  // namespace expr
}  // namespace CVC4
