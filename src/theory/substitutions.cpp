/*********************                                                        */
/*! \file substitutions.cpp
 ** \verbatim
 ** Original author: dejan
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

#include "theory/substitutions.h"

using namespace std;

namespace CVC4 {
namespace theory {

struct substitution_stack_element {
  TNode node;
  bool children_added;
  substitution_stack_element(TNode node)
  : node(node), children_added(false) {}
};

Node SubstitutionMap::internalSubstitute(TNode t, NodeCache& substitutionCache) {

  Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << ")" << std::endl;

  // If nothing to substitute just return the node
  if (substitutionCache.empty()) {
    return t;
  }

  // Do a topological sort of the subexpressions and substitute them
  vector<substitution_stack_element> toVisit;
  toVisit.push_back((TNode) t);

  while (!toVisit.empty())
  {
    // The current node we are processing
    substitution_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): processing " << current << std::endl;

    // If node already in the cache we're done, pop from the stack
    NodeCache::iterator find = substitutionCache.find(current);
    if (find != substitutionCache.end()) {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added) {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(substitutionCache.find(current[i]) != substitutionCache.end());
        builder << Node(substitutionCache[current[i]]);
      }
      // Mark the substitution and continue
      Node result = builder;
      Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): setting " << current << " -> " << result << std::endl;
      substitutionCache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeCache::iterator childFind = substitutionCache.find(childNode);
          if (childFind == substitutionCache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): setting " << current << " -> " << current << std::endl;
        substitutionCache[current] = current;
        toVisit.pop_back();
      }
    }
  }

  // Return the substituted version
  return substitutionCache[t];
}

void SubstitutionMap::addSubstitution(TNode x, TNode t, bool invalidateCache) {
  Debug("substitution") << "SubstitutionMap::addSubstitution(" << x << ", " << t << ")" << std::endl;
  Assert(d_substitutions.find(x) == d_substitutions.end());

  // Temporary substitution cache
  NodeCache tempCache;
  tempCache[x] = t;

  // Put in the new substitutions into the old ones
  NodeMap::iterator it = d_substitutions.begin();
  NodeMap::iterator it_end = d_substitutions.end();
  for(; it != it_end; ++ it) {
    d_substitutions[(*it).first] = internalSubstitute((*it).second, tempCache);
  }

  // Put the new substitution in
  d_substitutions[x] = t;

  // Also invalidate the cache
  if (invalidateCache) {
    d_cacheInvalidated = true;
  }
}

static bool check(TNode node, const SubstitutionMap::NodeMap& substitutions) CVC4_UNUSED;
static bool check(TNode node, const SubstitutionMap::NodeMap& substitutions) {
  SubstitutionMap::NodeMap::const_iterator it = substitutions.begin();
  SubstitutionMap::NodeMap::const_iterator it_end = substitutions.end();
  Debug("substitution") << "checking " << node << std::endl;
  for (; it != it_end; ++ it) {
    Debug("substitution") << "-- hasSubterm( " << (*it).first << " ) ?" << std::endl;
    if (node.hasSubterm((*it).first)) {
      Debug("substitution") << "-- FAIL" << std::endl;
      return false;
    }
  }
  Debug("substitution") << "-- SUCCEED" << std::endl;
  return true;
}

Node SubstitutionMap::apply(TNode t) {

  Debug("substitution") << "SubstitutionMap::apply(" << t << ")" << std::endl;

  // Setup the cache
  if (d_cacheInvalidated) {
    SubstitutionMap::NodeMap::const_iterator it = d_substitutions.begin();
    SubstitutionMap::NodeMap::const_iterator it_end = d_substitutions.end();
    d_substitutionCache.clear();
    for (; it != it_end; ++ it) {
      d_substitutionCache[(*it).first] = (*it).second;
    }
    d_cacheInvalidated = false;
    Debug("substitution") << "-- reset the cache" << std::endl;
  }

  SubstitutionMap::NodeMap::const_iterator it = d_substitutions.begin();
  SubstitutionMap::NodeMap::const_iterator it_end = d_substitutions.end();
  for (; it != it_end; ++ it) {
    Debug("substitution") << "substs has ( " << (*it).first << " => " << (*it).second << " )" << std::endl;
  }

  SubstitutionMap::NodeCache::const_iterator iit = d_substitutionCache.begin();
  SubstitutionMap::NodeCache::const_iterator iit_end = d_substitutionCache.end();
  for (; iit != iit_end; ++ iit) {
    Debug("substitution") << "CACHE has ( " << (*iit).first << " => " << (*iit).second << " )" << std::endl;
  }

  // Perform the substitution
  Node result = internalSubstitute(t, d_substitutionCache);
  Debug("substitution") << "SubstitutionMap::apply(" << t << ") => " << result << std::endl;

  Assert(check(result, d_substitutions));

  return result;
}

void SubstitutionMap::print(ostream& out) const {
  NodeMap::const_iterator it = d_substitutions.begin();
  NodeMap::const_iterator it_end = d_substitutions.end();
  for (; it != it_end; ++ it) {
    out << (*it).first << " -> " << (*it).second << endl;
  }
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
