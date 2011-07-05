/*********************                                                        */
/*! \file substitutions.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A substitution mapping for theory simplification
 **
 ** A substitution mapping for theory simplification.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SUBSTITUTIONS_H
#define __CVC4__THEORY__SUBSTITUTIONS_H

#include <utility>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/**
 * The type for the Substitutions mapping output by
 * Theory::simplify(), TheoryEngine::simplify(), and
 * Valuation::simplify().  This is in its own header to avoid circular
 * dependences between those three.
 */
class SubstitutionMap {

public:

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;

private:

  /** The variables, in order of addition */
  NodeMap d_substitutions;

  /** Cache of the already performed substitutions */
  NodeMap d_substitutionCache;

  /** Has the cache been invalidated */
  bool d_cacheInvalidated;

  /** Internaal method that performs substitution */
  Node internalSubstitute(TNode t, NodeMap& substitutionCache);

public:

  SubstitutionMap(): d_cacheInvalidated(true) {}

  /**
   * Adds a substitution from x to t
   */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);


  /**
   * Apply the substitutions to the node.
   */
  Node apply(TNode t);

  /**
   * Apply the substitutions to the node.
   */
  Node apply(TNode t) const {
    return const_cast<SubstitutionMap*>(this)->apply(t);
  }

  /**
   * Print to the output stream
   */
  void print(std::ostream& out) const;

};

inline std::ostream& operator << (std::ostream& out, const SubstitutionMap& subst) {
  subst.print(out);
  return out;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SUBSTITUTIONS_H */
