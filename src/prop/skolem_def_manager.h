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

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/node.h"

namespace CVC4 {

class RemoveTermFormulas;

namespace prop {

/**
 * This class manages the mapping between literals, the skolem they contain,
 * and the definitions for the skolems.
 */
class SkolemDefManager
{
  using NodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  SkolemDefManager(context::Context* context,
                   context::UserContext* userContext,
                   RemoveTermFormulas& rtf);

  ~SkolemDefManager();

  /** Notify skolem definitions */
  void notifySkolemDefinition(TNode skolem, TNode def);
  /** Get skolem definition for skolem */
  TNode getSkolemDefinitionFor(TNode skolem) const;
  /**
   * Notify asserted literal, adds additionally activated skolems into queue.
   */
  void notifyAsserted(TNode literal, std::vector<TNode>& activatedSkolems);

 private:
  /** Reference to term formula removal */
  RemoveTermFormulas& d_rtf;
  /** skolems to definitions (user-context dependent) */
  NodeMap d_skDefs;
  /** set of active skolems (SAT-context dependent) */
  NodeSet d_skActive;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SKOLEM_DEF_MANAGER_H */
