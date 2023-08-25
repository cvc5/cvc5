/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A substitution mapping for theory simplification.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SUBSTITUTIONS_H
#define CVC5__THEORY__SUBSTITUTIONS_H

//#include <algorithm>
#include <utility>
#include <vector>
#include <unordered_map>

#include "expr/node.h"
#include "context/context.h"
#include "context/cdo.h"
#include "context/cdhashmap.h"
#include "util/hash.h"

namespace cvc5::internal {
namespace theory {

class Rewriter;

/**
 * The type for the Substitutions mapping output by
 * Theory::simplify(), TheoryEngine::simplify(), and
 * Valuation::simplify().  This is in its own header to
 * avoid circular dependences between those three.
 *
 * This map is context-dependent.
 */
class SubstitutionMap
{
 public:
  typedef context::CDHashMap<Node, Node> NodeMap;

  typedef NodeMap::iterator iterator;
  typedef NodeMap::const_iterator const_iterator;

  struct ShouldTraverseCallback
  {
    virtual bool operator()(TNode n) const = 0;
    virtual ~ShouldTraverseCallback() {}
  };

 private:
  typedef std::unordered_map<Node, Node> NodeCache;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;

  /** The variables, in order of addition */
  NodeMap d_substitutions;

  /** Cache of the already performed substitutions */
  NodeCache d_substitutionCache;

  /** Has the cache been invalidated? */
  bool d_cacheInvalidated;

  /** Internal method that performs substitution */
  Node internalSubstitute(TNode t,
                          NodeCache& cache,
                          std::set<TNode>* tracker,
                          const ShouldTraverseCallback* stc);

  /** Helper class to invalidate cache on user pop */
  class CacheInvalidator : public context::ContextNotifyObj
  {
    bool& d_cacheInvalidated;

   protected:
    void contextNotifyPop() override { d_cacheInvalidated = true; }

   public:
    CacheInvalidator(context::Context* context, bool& cacheInvalidated)
        : context::ContextNotifyObj(context),
          d_cacheInvalidated(cacheInvalidated)
    {
    }

  }; /* class SubstitutionMap::CacheInvalidator */

  /**
   * This object is notified on user pop and marks the SubstitutionMap's
   * cache as invalidated.
   */
  CacheInvalidator d_cacheInvalidator;

 public:
  SubstitutionMap(context::Context* context = nullptr);

  /** Get substitutions in this object as a raw map */
  std::unordered_map<Node, Node> getSubstitutions() const;
  /**
   * Adds a substitution from x to t.
   */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);

  /**
   * Merge subMap into current set of substitutions
   */
  void addSubstitutions(SubstitutionMap& subMap, bool invalidateCache = true);

  /** Size of the substitutions */
  size_t size() const { return d_substitutions.size(); }
  /**
   * Returns true iff x is in the substitution map
   */
  bool hasSubstitution(TNode x) const
  {
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
  TNode getSubstitution(TNode x) const
  {
    AssertArgument(
        hasSubstitution(x), x, "element not in this substitution map");
    return (*d_substitutions.find(x)).second;
  }

  /**
   * Apply the substitutions to the node, optionally rewrite if a non-null
   * Rewriter pointer is passed.
   */
  Node apply(TNode t,
             Rewriter* r = nullptr,
             std::set<TNode>* tracker = nullptr,
             const ShouldTraverseCallback* stc = nullptr);

  /**
   * Apply the substitutions to the node.
   */
  Node apply(TNode t, Rewriter* r = nullptr) const
  {
    return const_cast<SubstitutionMap*>(this)->apply(t, r);
  }

  iterator begin() { return d_substitutions.begin(); }

  iterator end() { return d_substitutions.end(); }

  const_iterator begin() const { return d_substitutions.begin(); }

  const_iterator end() const { return d_substitutions.end(); }

  bool empty() const { return d_substitutions.empty(); }

  /**
   * Print to the output stream
   */
  void print(std::ostream& out) const;

  void invalidateCache() {
    d_cacheInvalidated = true;
  }

}; /* class SubstitutionMap */

inline std::ostream& operator << (std::ostream& out, const SubstitutionMap& subst) {
  subst.print(out);
  return out;
}

}  // namespace theory

std::ostream& operator<<(std::ostream& out, const theory::SubstitutionMap::iterator& i);

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SUBSTITUTIONS_H */
