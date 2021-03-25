/*********************                                                        */
/*! \file trigger_trie.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief trigger trie class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H
#define CVC4__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H

#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/ematching/trigger_database.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

  TriggerDatabase::TriggerDatabase(
                      QuantifiersState& qs,
                      QuantifiersInferenceManager& qim,
                      QuantifiersRegistry& qr,
                      TermRegistry& tr);
  TriggerDatabase::~TriggerDatabase() {}
  /**
   * This returns a Trigger t that is indexed by nodes, or nullptr otherwise.
   */
  Trigger* TriggerDatabase::::getTrigger(std::vector<Node>& nodes);
  /**
   * This adds t to the trie, indexed by nodes. In typical use cases, nodes i
   * t->d_nodes.
   */
  void TriggerDatabase::::addTrigger(std::vector<Node>& nodes, Trigger* t);

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__TRIGGER_DATABASE_H */
