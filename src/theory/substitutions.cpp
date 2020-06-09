/*********************                                                        */
/*! \file substitutions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Clark Barrett, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A substitution mapping for theory simplification
 **
 ** A substitution mapping for theory simplification.
 **/

#include "theory/substitutions.h"
#include "expr/node_algorithm.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {

struct substitution_stack_element {
  TNode d_node;
  bool d_children_added;
  substitution_stack_element(TNode node) : d_node(node), d_children_added(false)
  {
  }
};/* struct substitution_stack_element */

Node SubstitutionMap::internalSubstitute(TNode t, NodeCache& cache) {

  Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << ")" << endl;

  if (d_substitutions.empty()) {
    return t;
  }

  // Do a topological sort of the subexpressions and substitute them
  vector<substitution_stack_element> toVisit;
  toVisit.push_back((TNode) t);

  while (!toVisit.empty())
  {
    // The current node we are processing
    substitution_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.d_node;

    Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): processing " << current << endl;

    // If node already in the cache we're done, pop from the stack
    NodeCache::iterator find = cache.find(current);
    if (find != cache.end()) {
      toVisit.pop_back();
      continue;
    }

    if (!d_substituteUnderQuantifiers && current.isClosure())
    {
      Debug("substitution::internal") << "--not substituting under quantifier" << endl;
      cache[current] = current;
      toVisit.pop_back();
      continue;
    }

    NodeMap::iterator find2 = d_substitutions.find(current);
    if (find2 != d_substitutions.end()) {
      Node rhs = (*find2).second;
      Assert(rhs != current);
      internalSubstitute(rhs, cache);
      d_substitutions[current] = cache[rhs];
      cache[current] = cache[rhs];
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.d_children_added)
    {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << Node(cache[current.getOperator()]);
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(cache.find(current[i]) != cache.end());
        builder << Node(cache[current[i]]);
      }
      // Mark the substitution and continue
      Node result = builder;
      if (result != current) {
        find = cache.find(result);
        if (find != cache.end()) {
          result = find->second;
        }
        else {
          find2 = d_substitutions.find(result);
          if (find2 != d_substitutions.end()) {
            Node rhs = (*find2).second;
            Assert(rhs != result);
            internalSubstitute(rhs, cache);
            d_substitutions[result] = cache[rhs];
            cache[result] = cache[rhs];
            result = cache[rhs];
          }
        }
      }
      Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): setting " << current << " -> " << result << endl;
      cache[current] = result;
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0 || current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        stackHead.d_children_added = true;
        // We need to add the operator, if any
        if(current.getMetaKind() == kind::metakind::PARAMETERIZED) {
          TNode opNode = current.getOperator();
          NodeCache::iterator opFind = cache.find(opNode);
          if (opFind == cache.end()) {
            toVisit.push_back(opNode);
          }
        }
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeCache::iterator childFind = cache.find(childNode);
          if (childFind == cache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): setting " << current << " -> " << current << endl;
        cache[current] = current;
        toVisit.pop_back();
      }
    }
  }

  // Return the substituted version
  return cache[t];
}/* SubstitutionMap::internalSubstitute() */


void SubstitutionMap::simplifyRHS(const SubstitutionMap& subMap)
{
  // Put the new substitutions into the old ones
  NodeMap::iterator it = d_substitutions.begin();
  NodeMap::iterator it_end = d_substitutions.end();
  for(; it != it_end; ++ it) {
    d_substitutions[(*it).first] = subMap.apply((*it).second);
  }  
}


void SubstitutionMap::simplifyRHS(TNode x, TNode t) {
  // Temporary substitution cache
  NodeCache tempCache;
  tempCache[x] = t;

  // Put the new substitution into the old ones
  NodeMap::iterator it = d_substitutions.begin();
  NodeMap::iterator it_end = d_substitutions.end();
  for(; it != it_end; ++ it) {
    d_substitutions[(*it).first] = internalSubstitute((*it).second, tempCache);
  }  
  // it = d_substitutionsLazy.begin();
  // it_end = d_substitutionsLazy.end();
  // for(; it != it_end; ++ it) {
  //   d_substitutionsLazy[(*it).first] = internalSubstitute((*it).second, tempCache);
  // }  
}


void SubstitutionMap::addSubstitution(TNode x, TNode t, bool invalidateCache)
{
  Debug("substitution") << "SubstitutionMap::addSubstitution(" << x << ", " << t << ")" << endl;
  Assert(d_substitutions.find(x) == d_substitutions.end());

  // this causes a later assert-fail (the rhs != current one, above) anyway
  // putting it here is easier to diagnose
  Assert(x != t) << "cannot substitute a term for itself";

  d_substitutions[x] = t;

  // Also invalidate the cache if necessary
  if (invalidateCache) {
    d_cacheInvalidated = true;
  }
  else {
    d_substitutionCache[x] = d_substitutions[x];
  }
}


void SubstitutionMap::addSubstitutions(SubstitutionMap& subMap, bool invalidateCache)
{
  SubstitutionMap::NodeMap::const_iterator it = subMap.begin();
  SubstitutionMap::NodeMap::const_iterator it_end = subMap.end();
  for (; it != it_end; ++ it) {
    Assert(d_substitutions.find((*it).first) == d_substitutions.end());
    d_substitutions[(*it).first] = (*it).second;
    if (!invalidateCache) {
      d_substitutionCache[(*it).first] = d_substitutions[(*it).first];
    }
  }
  if (invalidateCache) {
    d_cacheInvalidated = true;
  }
}

static bool check(TNode node,
                  const SubstitutionMap::NodeMap& substitutions) CVC4_UNUSED;
static bool check(TNode node, const SubstitutionMap::NodeMap& substitutions)
{
  SubstitutionMap::NodeMap::const_iterator it = substitutions.begin();
  SubstitutionMap::NodeMap::const_iterator it_end = substitutions.end();
  Debug("substitution") << "checking " << node << endl;
  for (; it != it_end; ++it)
  {
    Debug("substitution") << "-- hasSubterm( " << (*it).first << " ) ?" << endl;
    if (expr::hasSubterm(node, (*it).first))
    {
      Debug("substitution") << "-- FAIL" << endl;
      return false;
    }
  }
  Debug("substitution") << "-- SUCCEED" << endl;
  return true;
}

Node SubstitutionMap::apply(TNode t) {

  Debug("substitution") << "SubstitutionMap::apply(" << t << ")" << endl;

  // Setup the cache
  if (d_cacheInvalidated) {
    d_substitutionCache.clear();
    d_cacheInvalidated = false;
    Debug("substitution") << "-- reset the cache" << endl;
  }

  // Perform the substitution
  Node result = internalSubstitute(t, d_substitutionCache);
  Debug("substitution") << "SubstitutionMap::apply(" << t << ") => " << result << endl;

  //  Assert(check(result, d_substitutions));

  return result;
}

void SubstitutionMap::print(ostream& out) const {
  NodeMap::const_iterator it = d_substitutions.begin();
  NodeMap::const_iterator it_end = d_substitutions.end();
  for (; it != it_end; ++ it) {
    out << (*it).first << " -> " << (*it).second << endl;
  }
}

void SubstitutionMap::debugPrint() const {
  print(Message.getStream());
}

}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, const theory::SubstitutionMap::iterator& i) {
  return out << "[CDMap-iterator]";
}

}/* CVC4 namespace */
