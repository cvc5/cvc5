/*********************                                                        */
/*! \file term_formula_removal.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Removal of term formulas
 **
 ** Removal of term formulas.
 **/

#include "cvc4_private.h"

#pragma once

#include <vector>

#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/dump.h"
#include "util/bool.h"
#include "util/hash.h"

namespace CVC4 {

namespace theory {
  class ContainsTermITEVisitor;
}/* CVC4::theory namespace */

typedef std::hash_map<Node, unsigned, NodeHashFunction> IteSkolemMap;

class RemoveTermFormulas {
  typedef context::CDInsertHashMap< std::pair<Node, int>, Node, PairHashFunction<Node, int, NodeHashFunction, BoolHashFunction> > ITECache;
  ITECache d_iteCache;

  static inline int cacheVal( bool inQuant, bool inTerm ) { return (inQuant ? 1 : 0) + 2*(inTerm ? 1 : 0); }
public:

  RemoveTermFormulas(context::UserContext* u);
  ~RemoveTermFormulas();

  /**
   * Removes the ITE nodes by introducing skolem variables. All
   * additional assertions are pushed into assertions. iteSkolemMap
   * contains a map from introduced skolem variables to the index in
   * assertions containing the new Boolean ite created in conjunction
   * with that skolem variable.
   *
   * With reportDeps true, report reasoning dependences to the proof
   * manager (for unsat cores).
   */
  void run(std::vector<Node>& assertions, IteSkolemMap& iteSkolemMap, bool reportDeps = false);

  /**
   * Removes the ITE from the node by introducing skolem
   * variables. All additional assertions are pushed into
   * assertions. iteSkolemMap contains a map from introduced skolem
   * variables to the index in assertions containing the new Boolean
   * ite created in conjunction with that skolem variable.
   */
  Node run(TNode node, std::vector<Node>& additionalAssertions,
           IteSkolemMap& iteSkolemMap, bool inQuant, bool inTerm);

  /**
   * Substitute under node using pre-existing cache.  Do not remove
   * any ITEs not seen during previous runs.
   */
  Node replace(TNode node, bool inQuant = false, bool inTerm = false) const;

  /** Returns true if e contains a term ite. */
  bool containsTermITE(TNode e) const;

  /** Returns the collected size of the caches. */
  size_t collectedCacheSizes() const;

  /** Garbage collects non-context dependent data-structures. */
  void garbageCollect();

  /** Return the RemoveTermFormulas's containsVisitor. */
  theory::ContainsTermITEVisitor* getContainsVisitor();

private:
  theory::ContainsTermITEVisitor* d_containsVisitor;

};/* class RemoveTTE */

}/* CVC4 namespace */
