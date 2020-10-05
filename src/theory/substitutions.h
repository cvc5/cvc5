/*********************                                                        */
/*! \file substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A substitution mapping for theory simplification
 **
 ** A substitution mapping for theory simplification.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SUBSTITUTIONS_H
#define CVC4__THEORY__SUBSTITUTIONS_H

//#include <algorithm>
#include <utility>
#include <vector>
#include <unordered_map>

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

  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeCache;

  /** The variables, in order of addition */
  NodeMap d_substitutions;

  /** Cache of the already performed substitutions */
  NodeCache d_substitutionCache;

  /** Whether or not to substitute under quantifiers */
  bool d_substituteUnderQuantifiers;

  /** Has the cache been invalidated? */
  bool d_cacheInvalidated;

  /** Internal method that performs substitution */
  Node internalSubstitute(TNode t, NodeCache& cache);

  /** Helper class to invalidate cache on user pop */
  class CacheInvalidator : public context::ContextNotifyObj {
    bool& d_cacheInvalidated;
  protected:
   void contextNotifyPop() override { d_cacheInvalidated = true; }

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
 SubstitutionMap(context::Context* context,
                 bool substituteUnderQuantifiers = true)
     : d_substitutions(context),
       d_substitutionCache(),
       d_substituteUnderQuantifiers(substituteUnderQuantifiers),
       d_cacheInvalidated(false),
       d_cacheInvalidator(context, d_cacheInvalidated)
 {
  }

  /**
   * Adds a substitution from x to t.
   */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);

  /**
   * Merge subMap into current set of substitutions
   */
  void addSubstitutions(SubstitutionMap& subMap, bool invalidateCache = true);

  /**
   * Returns true iff x is in the substitution map
   */
  bool hasSubstitution(TNode x) const {
    return d_substitutions.find(x) != d_substitutions.end();
  }

  /**
   * Returns the substitution mapping that was given for x via
   * addSubstitution().  Note that the returned value might itself
   * be in the map; for the actual substitution that would be
   * performed for x, use .apply(x).  This getSubstitution() function
   * is mainly intended for constructing assertions about what has
   * already been put in the map.
   */
  TNode getSubstitution(TNode x) const {
    AssertArgument(hasSubstitution(x), x, "element not in this substitution map");
    return (*d_substitutions.find(x)).second;
  }

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

  bool empty() const {
    return d_substitutions.empty();
  }

  /**
   * Print to the output stream
   */
  void print(std::ostream& out) const;
  void debugPrint() const;

};/* class SubstitutionMap */

inline std::ostream& operator << (std::ostream& out, const SubstitutionMap& subst) {
  subst.print(out);
  return out;
}

}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, const theory::SubstitutionMap::iterator& i);

}/* CVC4 namespace */

#endif /* CVC4__THEORY__SUBSTITUTIONS_H */
