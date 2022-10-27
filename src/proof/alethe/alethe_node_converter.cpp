/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"

namespace cvc5::internal {
namespace proof {

AletheNodeConverter::AletheNodeConverter() {}

Node AletheNodeConverter::convert(Node n)
{
  Trace("alethe-conv") << "AletheNodeConverter::convert: " << n << "\n";
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_cache.find(cur);
    Trace("alethe-conv2") << "convert " << cur << "\n";
    Kind k = cur.getKind();
    if (it == d_cache.end())
    {
      if (!shouldTraverse(cur))
      {
        d_cache[cur] = cur;
        continue;
      }
      d_cache[cur] = Node::null();
      visit.push_back(cur);
      if (k == kind::SKOLEM || k == kind::BOOLEAN_TERM_VARIABLE)
      {
        Trace("alethe-conv")
            << "AletheNodeConverter: [PRE] handling skolem " << cur << "\n";
        Node wi = SkolemManager::getWitnessForm(cur);
        // true skolem with witness form, just convert that
        if (!wi.isNull())
        {
          Trace("alethe-conv") << "AletheNodeConverter: ..skolem "
                               << cur << " has witness form " << wi << "\n";
          visit.push_back(wi);
        }
        else
        {
          // purification skolem, thus we need to build the fake choice term
          AlwaysAssert(!SkolemManager::getOriginalForm(cur).isNull());
          visit.push_back(SkolemManager::getOriginalForm(cur));
          Trace("alethe-conv") << "AletheNodeConverter: ..push original form "
                               << visit.back() << "\n";
        }
        continue;
      }
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      // collect children
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        it = d_cache.find(cur.getOperator());
        AlwaysAssert(it != d_cache.end());
        AlwaysAssert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
      }
      for (const Node& cn : cur)
      {
        it = d_cache.find(cn);
        AlwaysAssert(it != d_cache.end());
        AlwaysAssert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      // Now convert
      Node res;
      size_t nChildren = cur.getNumChildren();
      std::vector<Node> resChildren;
      Trace("alethe-conv") << "AletheNodeConverter: [POST] handling " << k << ", "
                           << cur << "\n";
      switch (k)
      {
        case kind::SKOLEM:
        case kind::BOOLEAN_TERM_VARIABLE:
        {
          Trace("alethe-conv")
              << "AletheNodeConverter: ..handling skolem " << cur << "\n";
          Node wi = SkolemManager::getWitnessForm(cur);
          // true skolem with witness form, just convert that
          if (!wi.isNull())
          {
            Trace("alethe-conv")
                << "AletheNodeConverter: ..skolem has witness form " << wi
                << ", converted to " << d_cache[wi] << "\n";
            res = d_cache[wi];
          }
          else
          {
            // purification skolem, thus we retrieve the conversion of its
            // original form
            AlwaysAssert(!SkolemManager::getOriginalForm(cur).isNull());
            Trace("alethe-conv")
                << "AletheNodeConverter: ..skolem has original form "
                << SkolemManager::getOriginalForm(cur) << ", converted to "
                << SkolemManager::getOriginalForm(cur) << "\n";
            res = d_cache[SkolemManager::getOriginalForm(cur)];
          }
          AlwaysAssert(!res.isNull());
          break;
        }
        case kind::FORALL:
        {
          if (nChildren == 3)
          {
            res = nm->mkNode(kind::FORALL, children[0], children[1]);
          }
          break;
        }
        default:
        {
          res = childChanged ? nm->mkNode(k, children) : Node(cur);
        }
      }
      d_cache[cur] = res;
      // force idempotency
      d_cache[res] = res;
    }
  } while (!visit.empty());
  Trace("lean-conv") << "LeanConverter::convert: for " << n << " returns "
                     << d_cache[n] << "\n";
  Assert(d_cache.find(n) != d_cache.end());
  Assert(!d_cache.find(n)->second.isNull());
  return d_cache[n];
}

bool AletheNodeConverter::shouldTraverse(Node n) { return true; }

}  // namespace proof
}  // namespace cvc5::internal
