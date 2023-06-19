/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trigger trie class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TRIGGER_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__TRIGGER_TRIE_H

#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/ematching/trigger.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** A trie of triggers.
 *
 * This class is used to cache all Trigger objects that are generated in the
 * current context. We index Triggers in this data structure based on the
 * value of Trigger::d_nodes. When a Trigger is added to this data structure,
 * this Trie assumes responsibility for deleting it.
 */
class TriggerTrie
{
 public:
  TriggerTrie();
  ~TriggerTrie();
  /**
   * This returns a Trigger t that is indexed by nodes, or nullptr otherwise.
   */
  Trigger* getTrigger(const std::vector<Node>& nodes);
  /**
   * This adds t to the trie, indexed by nodes. In typical use cases, nodes i
   * t->d_nodes.
   */
  void addTrigger(const std::vector<Node>& nodes, Trigger* t);
 private:
  /** The trigger at this node in the trie. */
  std::vector<Trigger*> d_tr;
  /** The children of this node in the trie. */
  std::map<Node, TriggerTrie> d_children;
}; /* class inst::Trigger::TriggerTrie */

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TRIGGER_TRIE_H */
