/*********************                                                        */
/*! \file term_formula_removal.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#include <unordered_map>
#include <vector>

#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "expr/node.h"
#include "smt/dump.h"
#include "util/bool.h"
#include "util/hash.h"

namespace CVC4 {

typedef std::unordered_map<Node, unsigned, NodeHashFunction> IteSkolemMap;

class RemoveTermFormulas {
  typedef context::
      CDInsertHashMap<std::pair<Node, int>,
                      Node,
                      PairHashFunction<Node, int, NodeHashFunction> >
          TermFormulaCache;
  /** term formula removal cache
   *
   * This stores the results of term formula removal for inputs to the run(...)
   * function below, where the integer in the pair we hash on is the
   * result of cacheVal below.
   */
  TermFormulaCache d_tfCache;

  /** return the integer cache value for the input flags to run(...) */
  static inline int cacheVal( bool inQuant, bool inTerm ) { return (inQuant ? 1 : 0) + 2*(inTerm ? 1 : 0); }

  /** skolem cache
   *
   * This is a cache that maps terms to the skolem we use to replace them.
   *
   * Notice that this cache is necessary in addition to d_tfCache, since
   * we should use the same skolem to replace terms, regardless of the input
   * arguments to run(...). For example:
   *
   * ite( G, a, b ) = c ^ forall x. P( ite( G, a, b ), x )
   *
   * should be processed to:
   *
   * k = c ^ forall x. P( k, x ) ^ ite( G, k=a, k=b )
   *
   * where notice
   *   d_skolem_cache[ite( G, a, b )] = k, and
   *   d_tfCache[<ite( G, a, b ),0>] = d_tfCache[<ite( G, a, b ),1>] = k.
   */
  context::CDInsertHashMap<Node, Node, NodeHashFunction> d_skolem_cache;

  /** gets the skolem for node
   *
   * This returns the d_skolem_cache value for node, if it exists as a key
   * in the above map, or the null node otherwise.
   */
  inline Node getSkolemForNode(Node node) const;

  static bool hasNestedTermChildren( TNode node );
public:

  RemoveTermFormulas(context::UserContext* u);
  ~RemoveTermFormulas();

  /**
   * By introducing skolem variables, this function removes all occurrences of:
   * (1) term ITEs,
   * (2) terms of type Boolean that are not Boolean term variables,
   * (3) lambdas, and
   * (4) Hilbert choice expressions.
   * from assertions.
   * All additional assertions are pushed into assertions. iteSkolemMap
   * contains a map from introduced skolem variables to the index in
   * assertions containing the new definition created in conjunction
   * with that skolem variable.
   *
   * As an example of (1):
   *   f( (ite C 0 1)) = 2
   * becomes
   *   f( k ) = 2 ^ ite( C, k=0, k=1 )
   *
   * As an example of (2):
   *   g( (and C1 C2) ) = 3
   * becomes
   *   g( k ) = 3 ^ ( k <=> (and C1 C2) )
   *
   * As an example of (3):
   *   (lambda x. t[x]) = f
   * becomes
   *   (forall x. k(x) = t[x]) ^ k = f
   * where k is a fresh skolem function.
   * This is sometimes called "lambda lifting"
   *
   * As an example of (4):
   *   (witness x. P( x ) ) = t
   * becomes
   *   P( k ) ^ k = t
   * where k is a fresh skolem constant.
   *
   * With reportDeps true, report reasoning dependences to the proof
   * manager (for unsat cores).
   */
  void run(std::vector<Node>& assertions, IteSkolemMap& iteSkolemMap, bool reportDeps = false);

  /**
   * Removes terms of the form (1), (2), (3) described above from node.
   * All additional assertions are pushed into
   * assertions. iteSkolemMap contains a map from introduced skolem
   * variables to the index in assertions containing the new Boolean
   * ite created in conjunction with that skolem variable.
   *
   * inQuant is whether we are processing node in the body of quantified formula
   * inTerm is whether we are are processing node in a "term" position, that is, it is a subterm
   *        of a parent term that is not a Boolean connective.
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

  /** Garbage collects non-context dependent data-structures. */
  void garbageCollect();
};/* class RemoveTTE */

}/* CVC4 namespace */
