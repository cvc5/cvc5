/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem definition manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SKOLEM_DEF_MANAGER_H
#define CVC5__PROP__SKOLEM_DEF_MANAGER_H

#include <iosfwd>
#include <unordered_set>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/node.h"

namespace cvc5 {
namespace prop {

/**
 * This class manages the mapping between introduced skolems and the lemmas
 * that define their behavior. It can be used to manage which lemmas are
 * relevant in the current context, e.g. a lemma corresponding to a skolem
 * definition for k is relevant when k appears in an asserted literal.
 *
 * It also has utilities for tracking (in a SAT-context-dependent manner) which
 * skolems are "active", e.g. appear in any asserted literal.
 */
class SkolemDefManager
{
  using NodeNodeMap = context::CDInsertHashMap<Node, Node, NodeHashFunction>;
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  SkolemDefManager(context::Context* context,
                   context::UserContext* userContext);

  ~SkolemDefManager();

  /**
   * Notify skolem definition. This is called when a lemma def is added to the
   * SAT solver that corresponds to the skolem definition for skolem k.
   */
  void notifySkolemDefinition(TNode k, Node def);
  /**
   * Get skolem definition for k, where k must be a skolem having a definition
   * managed by this class.
   */
  TNode getDefinitionForSkolem(TNode k) const;
  /**
   * Notify that the given literal has been asserted. This method adds skolems
   * that become "active" as a result of asserting this literal. A skolem
   * is active in the SAT context if it appears in an asserted literal.
   *
   * @param literal The literal that became asserted
   * @param activatedSkolems The list to add skolems to
   * @param useDefs If this flag is true, we add the skolem definition for
   * skolems to activatedSkolems instead of the skolem itself.
   */
  void notifyAsserted(TNode literal,
                      std::vector<TNode>& activatedSkolems,
                      bool useDefs = false);

  /**
   * Get the set of skolems maintained by this class that occur in node n,
   * add them to skolems.
   *
   * @param n The node to traverse
   * @param skolems The set where the skolems are added
   */
  void getSkolems(TNode n,
                  std::unordered_set<Node, NodeHashFunction>& skolems) const;
  /** Does n have skolems having definitions managed by this class? */
  bool hasSkolems(TNode n) const;

 private:
  /** skolems to definitions (user-context dependent) */
  NodeNodeMap d_skDefs;
  /** set of active skolems (SAT-context dependent) */
  NodeSet d_skActive;
};

}  // namespace prop
}  // namespace cvc5

#endif /* CVC5__PROP__SKOLEM_DEF_MANAGER_H */
