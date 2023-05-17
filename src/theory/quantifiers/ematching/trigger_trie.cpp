/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of trigger trie class.
 */

#include "theory/quantifiers/ematching/trigger_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

TriggerTrie::TriggerTrie() {}

TriggerTrie::~TriggerTrie()
{
  for (size_t i = 0, ntriggers = d_tr.size(); i < ntriggers; i++)
  {
    delete d_tr[i];
  }
}

inst::Trigger* TriggerTrie::getTrigger(const std::vector<Node>& nodes)
{
  std::vector<Node> temp;
  temp.insert(temp.begin(), nodes.begin(), nodes.end());
  std::sort(temp.begin(), temp.end());
  TriggerTrie* tt = this;
  for (const Node& n : temp)
  {
    std::map<Node, TriggerTrie>::iterator itt = tt->d_children.find(n);
    if (itt == tt->d_children.end())
    {
      return nullptr;
    }
    else
    {
      tt = &(itt->second);
    }
  }
  return tt->d_tr.empty() ? nullptr : tt->d_tr[0];
}

void TriggerTrie::addTrigger(const std::vector<Node>& nodes, inst::Trigger* t)
{
  std::vector<Node> temp(nodes.begin(), nodes.end());
  std::sort(temp.begin(), temp.end());
  TriggerTrie* tt = this;
  for (const Node& n : temp)
  {
    std::map<Node, TriggerTrie>::iterator itt = tt->d_children.find(n);
    if (itt == tt->d_children.end())
    {
      TriggerTrie* ttn = &tt->d_children[n];
      tt = ttn;
    }
    else
    {
      tt = &(itt->second);
    }
  }
  tt->d_tr.push_back(t);
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
