/*********************                                                        */
/*! \file skolem_def_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Skolem definition manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__SKOLEM_DEF_MANAGER_H
#define CVC4__PROP__SKOLEM_DEF_MANAGER_H

#include <iosfwd>
#include <unordered_set>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/node.h"

namespace CVC4 {
namespace prop {

/**
 * This class manages the mapping between introduced skolems and the lemmas
 * that define their behavior. It can be used to manage which lemmas are
 * relevant in the current context, e.g. a lemma corresponding to a skolem
 * definition for k is relevant when k appears in an asserted literal.
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
   * Notify skolem definition
   */
  void notifySkolemDefinition(TNode k, Node def);
  /** Get skolem definition for k */
  TNode getDefinitionForSkolem(TNode k) const;
  /**
   * Notify asserted literal, adds additionally activated skolems into queue.
   */
  void notifyAsserted(TNode literal, std::vector<TNode>& activatedSkolems);

  /**
   * Get the set of skolems introduced by this class that occur in node n,
   * add them to skolems.
   *
   * @param n The node to traverse
   * @param skolems The set where the skolems are added
   */
  void getSkolems(TNode n,
                  std::unordered_set<Node, NodeHashFunction>& skolems) const;
  /**
   * Does n have skolems introduced by this class?
   */
  bool hasSkolems(TNode n) const;

 private:
  /** skolems to definitions (user-context dependent) */
  NodeNodeMap d_skDefs;
  /** set of active skolems (SAT-context dependent) */
  NodeSet d_skActive;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SKOLEM_DEF_MANAGER_H */
