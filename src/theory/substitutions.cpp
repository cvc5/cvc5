/*********************                                                        */
/*! \file substitutions.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters, Clark Barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A substitution mapping for theory simplification
 **
 ** A substitution mapping for theory simplification.
 **/

#include "theory/substitutions.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {

struct substitution_stack_element {
  TNode node;
  bool children_added;
  substitution_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct substitution_stack_element */

Node SubstitutionMap::internalSubstitute(TNode t) {

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
    TNode current = stackHead.node;

    Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): processing " << current << endl;

    // If node already in the cache we're done, pop from the stack
    NodeCache::iterator find = d_substitutionCache.find(current);
    if (find != d_substitutionCache.end()) {
      toVisit.pop_back();
      continue;
    }

    if (!d_substituteUnderQuantifiers &&
        (current.getKind() == kind::FORALL || current.getKind() == kind::EXISTS)) {
      Debug("substitution::internal") << "--not substituting under quantifier" << endl;
      d_substitutionCache[current] = current;
      toVisit.pop_back();
      continue;
    }

    NodeMap::iterator find2 = d_substitutions.find(current);
    if (find2 != d_substitutions.end()) {
      Node rhs = (*find2).second;
      Assert(rhs != current);
      internalSubstitute(rhs);
      d_substitutions[current] = d_substitutionCache[rhs];
      d_substitutionCache[current] = d_substitutionCache[rhs];
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added) {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << Node(d_substitutionCache[current.getOperator()]);
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(d_substitutionCache.find(current[i]) != d_substitutionCache.end());
        builder << Node(d_substitutionCache[current[i]]);
      }
      // Mark the substitution and continue
      Node result = builder;
      if (result != current) {
        find = d_substitutionCache.find(result);
        if (find != d_substitutionCache.end()) {
          result = find->second;
        }
        else {
          find2 = d_substitutions.find(result);
          if (find2 != d_substitutions.end()) {
            Node rhs = (*find2).second;
            Assert(rhs != result);
            internalSubstitute(rhs);
            d_substitutions[result] = d_substitutionCache[rhs];
            d_substitutionCache[result] = d_substitutionCache[rhs];
            result = d_substitutionCache[rhs];
          }
        }
      }
      Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): setting " << current << " -> " << result << endl;
      d_substitutionCache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0 || current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        stackHead.children_added = true;
        // We need to add the operator, if any
        if(current.getMetaKind() == kind::metakind::PARAMETERIZED) {
          TNode opNode = current.getOperator();
          NodeCache::iterator opFind = d_substitutionCache.find(opNode);
          if (opFind == d_substitutionCache.end()) {
            toVisit.push_back(opNode);
          }
        }
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeCache::iterator childFind = d_substitutionCache.find(childNode);
          if (childFind == d_substitutionCache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << t << "): setting " << current << " -> " << current << endl;
        d_substitutionCache[current] = current;
        toVisit.pop_back();
      }
    }
  }

  // Return the substituted version
  return d_substitutionCache[t];
}/* SubstitutionMap::internalSubstitute() */


  /*
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
  NodeMap::iterator it = d_substitutionsOld.begin();
  NodeMap::iterator it_end = d_substitutionsOld.end();
  for(; it != it_end; ++ it) {
    d_substitutionsOld[(*it).first] = internalSubstituteOld((*it).second, tempCache);
  }  
  // it = d_substitutionsLazy.begin();
  // it_end = d_substitutionsLazy.end();
  // for(; it != it_end; ++ it) {
  //   d_substitutionsLazy[(*it).first] = internalSubstitute((*it).second, tempCache);
  // }  
}
*/

/* We use subMap to simplify the left-hand sides of the current substitution map.  If rewrite is true,
 * we also apply the rewriter to the result.
 * We want to maintain the invariant that all lhs are distinct from each other and from all rhs.
 * If for some l -> r, l reduces to l', we try to add a new rule l' -> r.  There are two cases
 * where this fails
 *   (i) if l' is equal to some ll (in a rule ll -> rr), then if r != rr we add (r,rr) to the equation list
 *   (i) if l' is equalto some rr (in a rule ll -> rr), then if r != rr we add (r,rr) to the equation list
 */
/*
void SubstitutionMap::simplifyLHS(const SubstitutionMap& subMap, vector<pair<Node, Node> >& equalities, bool rewrite)
{
  Assert(d_worklist.empty());
  // First, apply subMap to every LHS in d_substitutions
  NodeMap::iterator it = d_substitutions.begin();
  NodeMap::iterator it_end = d_substitutions.end();
  Node newLeft;
  for(; it != it_end; ++ it) {
    newLeft = subMap.apply((*it).first);
    if (newLeft != (*it).first) {
      if (rewrite) {
        newLeft = Rewriter::rewrite(newLeft);
      }
      d_worklist.push_back(pair<Node,Node>(newLeft, (*it).second));
    }
  }
  processWorklist(equalities, rewrite);
  Assert(d_worklist.empty());
}


void SubstitutionMap::simplifyLHS(TNode lhs, TNode rhs, vector<pair<Node,Node> >& equalities, bool rewrite)
{
  Assert(d_worklist.empty());
  d_worklist.push_back(pair<Node,Node>(lhs,rhs));
  processWorklist(equalities, rewrite);                       
  Assert(d_worklist.empty());
}


void SubstitutionMap::processWorklist(vector<pair<Node, Node> >& equalities, bool rewrite)
{
  // Add each new rewrite rule, taking care not to invalidate invariants and looking
  // for any new rewrite rules we can learn
  Node newLeft, newRight;
  while (!d_worklist.empty()) {
    newLeft = d_worklist.back().first;
    newRight = d_worklist.back().second;
    d_worklist.pop_back();

    NodeCache tempCache;
    tempCache[newLeft] = newRight;

    Node newLeft2;
    unsigned size = d_worklist.size();
    bool addThisRewrite = true;
    NodeMap::iterator it = d_substitutions.begin();
    NodeMap::iterator it_end = d_substitutions.end();

    for(; it != it_end; ++ it) {

      // Check for invariant violation.  If new rewrite is redundant, do nothing
      // Otherwise, add an equality to the output equalities
      // In either case undo any work done by this rewrite
      if (newLeft == (*it).first || newLeft == (*it).second) {
        if ((*it).second != newRight) {
          equalities.push_back(pair<Node,Node>((*it).second, newRight));
        }
        while (d_worklist.size() > size) {
          d_worklist.pop_back();
        }
        addThisRewrite = false;
        break;
      }

      newLeft2 = internalSubstituteOld((*it).first, tempCache);
      if (newLeft2 != (*it).first) {
        if (rewrite) {
          newLeft2 = Rewriter::rewrite(newLeft2);
        }
        d_worklist.push_back(pair<Node,Node>(newLeft2, (*it).second));
      }
    }
    if (addThisRewrite) {
      d_substitutions[newLeft] = newRight;
      d_cacheInvalidated = true;
    }
  }
}
*/

void SubstitutionMap::addSubstitution(TNode x, TNode t, bool invalidateCache)
{
  Debug("substitution") << "SubstitutionMap::addSubstitution(" << x << ", " << t << ")" << endl;
  Assert(d_substitutions.find(x) == d_substitutions.end());

  // this causes a later assert-fail (the rhs != current one, above) anyway
  // putting it here is easier to diagnose
  Assert(x != t, "cannot substitute a term for itself");

  d_substitutions[x] = t;

  // Also invalidate the cache if necessary
  if (invalidateCache) {
    d_cacheInvalidated = true;
  }
  else {
    d_substitutionCache[x] = d_substitutions[x];
  }
}

static bool check(TNode node, const SubstitutionMap::NodeMap& substitutions) CVC4_UNUSED;
static bool check(TNode node, const SubstitutionMap::NodeMap& substitutions) {
  SubstitutionMap::NodeMap::const_iterator it = substitutions.begin();
  SubstitutionMap::NodeMap::const_iterator it_end = substitutions.end();
  Debug("substitution") << "checking " << node << endl;
  for (; it != it_end; ++ it) {
    Debug("substitution") << "-- hasSubterm( " << (*it).first << " ) ?" << endl;
    if (node.hasSubterm((*it).first)) {
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
  Node result = internalSubstitute(t);
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
