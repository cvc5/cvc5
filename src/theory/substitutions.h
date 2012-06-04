/*********************                                                        */
/*! \file substitutions.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
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
#include <algorithm>

#include "expr/node.h"
#include "context/context.h"
#include "context/cdo.h"
#include "context/cdhashmap.h"
#include "util/hash.h"

namespace CVC4 {
namespace theory {

/**
 * The type for the Substitutions mapping output by
 * Theory::simplify(), TheoryEngine::simplify(), and
 * Valuation::simplify().  This is in its own header to
 * avoid circular dependences between those three.
 *
 * This map is context-dependent.
 */
class SubstitutionMap {

public:

  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

  typedef NodeMap::iterator iterator;
  typedef NodeMap::const_iterator const_iterator;

private:

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeCache;

  /** The context within which this SubstitutionMap was constructed. */
  context::Context* d_context;

  /** The variables, in order of addition */
  NodeMap d_substitutions;

  /** Cache of the already performed substitutions */
  NodeCache d_substitutionCache;

  /** Has the cache been invalidated? */
  bool d_cacheInvalidated;

  /** Internal method that performs substitution */
  Node internalSubstitute(TNode t, NodeCache& substitutionCache);

  /** Helper class to invalidate cache on user pop */
  class CacheInvalidator : public context::ContextNotifyObj {
    bool& d_cacheInvalidated;
  protected:
    void contextNotifyPop() {
      d_cacheInvalidated = true;
    }
  public:
    CacheInvalidator(context::Context* context, bool& cacheInvalidated) :
      context::ContextNotifyObj(context),
      d_cacheInvalidated(cacheInvalidated) {
    }

  };/* class SubstitutionMap::CacheInvalidator */

  /**
   * This object is notified on user pop and marks the SubstitutionMap's
   * cache as invalidated.
   */
  CacheInvalidator d_cacheInvalidator;

public:

  SubstitutionMap(context::Context* context) :
    d_context(context),
    d_substitutions(context),
    d_substitutionCache(),
    d_cacheInvalidated(false),
    d_cacheInvalidator(context, d_cacheInvalidated) {
  }

  /**
   * Adds a substitution from x to t
   */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);

  /**
   * Returns true iff x is in the substitution map
   */
  bool hasSubstitution(TNode x)
    { return d_substitutions.find(x) != d_substitutions.end(); }

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

  iterator begin() {
    return d_substitutions.begin();
  }

  iterator end() {
    return d_substitutions.end();
  }

  const_iterator begin() const {
    return d_substitutions.begin();
  }

  const_iterator end() const {
    return d_substitutions.end();
  }

  // NOTE [MGD]: removed clear() and swap() from the interface
  // when this data structure became context-dependent
  // because they weren't used---and it's not clear how they
  // should // best interact with cache invalidation on context
  // pops.

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

std::ostream& operator<<(std::ostream& out, const theory::SubstitutionMap::iterator& i);

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SUBSTITUTIONS_H */
