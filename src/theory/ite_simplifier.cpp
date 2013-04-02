/*********************                                                        */
/*! \file ite_simplifier.cpp
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simplifications for ITE expressions
 **
 ** This module implements preprocessing phases designed to simplify ITE
 ** expressions.  Based on:
 ** Kim, Somenzi, Jin.  Efficient Term-ITE Conversion for SMT.  FMCAD 2009.
 ** Burch, Jerry.  Techniques for Verifying Superscalar Microprocessors.  DAC '96
 **/


#include "theory/ite_simplifier.h"


using namespace std;
using namespace CVC4;
using namespace theory;


bool ITESimplifier::containsTermITE(TNode e)
{
  if (e.getKind() == kind::ITE && !e.getType().isBoolean()) {
    return true;
  }

  hash_map<Node, bool, NodeHashFunction>::iterator it;
  it = d_containsTermITECache.find(e); 
  if (it != d_containsTermITECache.end()) {
    return (*it).second;
  }

  size_t k = 0, sz = e.getNumChildren();
  for (; k < sz; ++k) {
    if (containsTermITE(e[k])) {
      d_containsTermITECache[e] = true;
      return true;
    }
  }

  d_containsTermITECache[e] = false;
  return false;
}


bool ITESimplifier::leavesAreConst(TNode e, TheoryId tid)
{
  Assert((e.getKind() == kind::ITE && !e.getType().isBoolean()) ||
         Theory::theoryOf(e) != THEORY_BOOL);
  if (e.isConst()) {
    return true;
  }

  hash_map<Node, bool, NodeHashFunction>::iterator it;
  it = d_leavesConstCache.find(e); 
  if (it != d_leavesConstCache.end()) {
    return (*it).second;
  }

  if (!containsTermITE(e) && Theory::isLeafOf(e, tid)) {
    d_leavesConstCache[e] = false;
    return false;
  }

  Assert(e.getNumChildren() > 0);
  size_t k = 0, sz = e.getNumChildren();

  if (e.getKind() == kind::ITE) {
    k = 1;
  }

  for (; k < sz; ++k) {
    if (!leavesAreConst(e[k], tid)) {
      d_leavesConstCache[e] = false;
      return false;
    }
  }
  d_leavesConstCache[e] = true;
  return true;
}


Node ITESimplifier::simpConstants(TNode simpContext, TNode iteNode, TNode simpVar)
{
  NodePairMap::iterator it;
  it = d_simpConstCache.find(pair<Node, Node>(simpContext,iteNode));
  if (it != d_simpConstCache.end()) {
    return (*it).second;
  }

  if (iteNode.getKind() == kind::ITE) {
    NodeBuilder<> builder(kind::ITE);
    builder << iteNode[0];
    unsigned i = 1;
    for (; i < iteNode.getNumChildren(); ++ i) {
      Node n = simpConstants(simpContext, iteNode[i], simpVar);
      if (n.isNull()) {
        return n;
      }
      builder << n;
    }
    // Mark the substitution and continue
    Node result = builder;
    result = Rewriter::rewrite(result);
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = result;
    return result;
  }

  if (!containsTermITE(iteNode)) {
    Node n = Rewriter::rewrite(simpContext.substitute(simpVar, iteNode));
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
    return n;
  }

  Node iteNode2;
  Node simpVar2;
  d_simpContextCache.clear();
  Node simpContext2 = createSimpContext(iteNode, iteNode2, simpVar2);
  if (!simpContext2.isNull()) {
    Assert(!iteNode2.isNull());
    simpContext2 = simpContext.substitute(simpVar, simpContext2);
    Node n = simpConstants(simpContext2, iteNode2, simpVar2);
    if (n.isNull()) {
      return n;
    }
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
    return n;
  }
  return Node();
}


Node ITESimplifier::getSimpVar(TypeNode t)
{
  std::hash_map<TypeNode, Node, TypeNode::HashFunction>::iterator it;
  it = d_simpVars.find(t);
  if (it != d_simpVars.end()) {
    return (*it).second;
  }
  else {
    Node var = NodeManager::currentNM()->mkSkolem("iteSimp_$$", t, "is a variable resulting from ITE simplification");
    d_simpVars[t] = var;
    return var;
  }
}


Node ITESimplifier::createSimpContext(TNode c, Node& iteNode, Node& simpVar)
{
  NodeMap::iterator it;
  it = d_simpContextCache.find(c);
  if (it != d_simpContextCache.end()) {
    return (*it).second;
  }

  if (!containsTermITE(c)) {
    d_simpContextCache[c] = c;
    return c;
  }

  if (c.getKind() == kind::ITE && !c.getType().isBoolean()) {
    // Currently only support one ite node in a simp context
    // Return Null if more than one is found
    if (!iteNode.isNull()) {
      return Node();
    }
    simpVar = getSimpVar(c.getType());
    if (simpVar.isNull()) {
      return Node();
    }
    d_simpContextCache[c] = simpVar;
    iteNode = c;
    return simpVar;
  }

  NodeBuilder<> builder(c.getKind());
  if (c.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << c.getOperator();
  }
  unsigned i = 0;
  for (; i < c.getNumChildren(); ++ i) {
    Node newChild = createSimpContext(c[i], iteNode, simpVar);
    if (newChild.isNull()) {
      return newChild;
    }
    builder << newChild;
  }
  // Mark the substitution and continue
  Node result = builder;
  d_simpContextCache[c] = result;
  return result;
}


Node ITESimplifier::simpITEAtom(TNode atom)
{
  if (leavesAreConst(atom)) {
    Node iteNode;
    Node simpVar;
    d_simpContextCache.clear();
    Node simpContext = createSimpContext(atom, iteNode, simpVar);
    if (!simpContext.isNull()) {
      if (iteNode.isNull()) {
        Assert(leavesAreConst(simpContext) && !containsTermITE(simpContext));
        return Rewriter::rewrite(simpContext);
      }
      Node n = simpConstants(simpContext, iteNode, simpVar);
      if (!n.isNull()) {
        return n;
      }
    }
  }
  return atom;
}


struct preprocess_stack_element {
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */


Node ITESimplifier::simpITE(TNode assertion)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    // If node has no ITE's or already in the cache we're done, pop from the stack
    if (current.getNumChildren() == 0 ||
        (Theory::theoryOf(current) != THEORY_BOOL && !containsTermITE(current))) {
       d_simpITECache[current] = current;
       toVisit.pop_back();
       continue;
    }

    NodeMap::iterator find = d_simpITECache.find(current);
    if (find != d_simpITECache.end()) {
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
        Assert(d_simpITECache.find(current[i]) != d_simpITECache.end());
        builder << d_simpITECache[current[i]];
      }
      // Mark the substitution and continue
      Node result = builder;

      // If this is an atom, we process it
      if (Theory::theoryOf(result) != THEORY_BOOL &&
          result.getType().isBoolean()) {
        result = simpITEAtom(result);
      }

      result = Rewriter::rewrite(result);
      d_simpITECache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_simpITECache.find(childNode);
          if (childFind == d_simpITECache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        d_simpITECache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  return d_simpITECache[assertion];
}


ITESimplifier::CareSetPtr ITESimplifier::getNewSet()
{
  if (d_usedSets.empty()) {
    return ITESimplifier::CareSetPtr::mkNew(*this);
  }
  else {
    ITESimplifier::CareSetPtr cs = ITESimplifier::CareSetPtr::recycle(d_usedSets.back());
    cs.getCareSet().clear();
    d_usedSets.pop_back();
    return cs;
  }
}


void ITESimplifier::updateQueue(CareMap& queue,
                               TNode e,
                               ITESimplifier::CareSetPtr& careSet)
{
  CareMap::iterator it = queue.find(e), iend = queue.end();
  if (it != iend) {
    set<Node>& cs2 = (*it).second.getCareSet();
    ITESimplifier::CareSetPtr csNew = getNewSet();
    set_intersection(careSet.getCareSet().begin(),
                     careSet.getCareSet().end(),
                     cs2.begin(), cs2.end(),
                     inserter(csNew.getCareSet(), csNew.getCareSet().begin()));
    (*it).second = csNew;
  }
  else {
    queue[e] = careSet;
  }
}


Node ITESimplifier::substitute(TNode e, TNodeMap& substTable, TNodeMap& cache)
{
  TNodeMap::iterator it = cache.find(e), iend = cache.end();
  if (it != iend) {
    return it->second;
  }

  // do substitution?
  it = substTable.find(e);
  iend = substTable.end();
  if (it != iend) {
    Node result = substitute(it->second, substTable, cache);
    cache[e] = result;
    return result;
  }

  size_t sz = e.getNumChildren();
  if (sz == 0) {
    cache[e] = e;
    return e;
  }

  NodeBuilder<> builder(e.getKind());
  if (e.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << e.getOperator();
  }
  for (unsigned i = 0; i < e.getNumChildren(); ++ i) {
    builder << substitute(e[i], substTable, cache);
  }

  Node result = builder;
  // it = substTable.find(result);
  // if (it != iend) {
  //   result = substitute(it->second, substTable, cache);
  // }
  cache[e] = result;
  return result;
}


Node ITESimplifier::simplifyWithCare(TNode e)
{
  TNodeMap substTable;
  CareMap queue;
  CareMap::iterator it;
  ITESimplifier::CareSetPtr cs = getNewSet();
  ITESimplifier::CareSetPtr cs2;
  queue[e] = cs;

  TNode v;
  bool done;
  unsigned i;

  while (!queue.empty()) {
    it = queue.end();
    --it;
    v = it->first;
    cs = it->second;
    set<Node>& css = cs.getCareSet();
    queue.erase(v);

    done = false;
    set<Node>::iterator iCare, iCareEnd = css.end();

    switch (v.getKind()) {
      case kind::ITE: {
        iCare = css.find(v[0]);
        if (iCare != iCareEnd) {
          Assert(substTable.find(v) == substTable.end());
          substTable[v] = v[1];
          updateQueue(queue, v[1], cs);
          done = true;
          break;
        }
        else {
          iCare = css.find(v[0].negate());
          if (iCare != iCareEnd) {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = v[2];
            updateQueue(queue, v[2], cs);
            done = true;
            break;
          }
        }
        updateQueue(queue, v[0], cs);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0]);
        updateQueue(queue, v[1], cs2);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0].negate());
        updateQueue(queue, v[2], cs2);
        done = true;
        break;
      }
      case kind::AND: {
        for (i = 0; i < v.getNumChildren(); ++i) {
          iCare = css.find(v[i].negate());
          if (iCare != iCareEnd) {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = d_false;
            done = true;
            break;
          }
        }
        if (done) break;

        Assert(v.getNumChildren() > 1);
        updateQueue(queue, v[0], cs);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0]);
        for (i = 1; i < v.getNumChildren(); ++i) {
          updateQueue(queue, v[i], cs2);
        }
        done = true;
        break;
      }
      case kind::OR: {
        for (i = 0; i < v.getNumChildren(); ++i) {
          iCare = css.find(v[i]);
          if (iCare != iCareEnd) {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = d_true;
            done = true;
            break;
          }
        }
        if (done) break;

        Assert(v.getNumChildren() > 1);
        updateQueue(queue, v[0], cs);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0].negate());
        for (i = 1; i < v.getNumChildren(); ++i) {
          updateQueue(queue, v[i], cs2);
        }
        done = true;
        break;
      }
      default:
        break;
    }

    if (done) {
      continue;
    }

    for (unsigned i = 0; i < v.getNumChildren(); ++i) {
      updateQueue(queue, v[i], cs);
    }
  }
  while (!d_usedSets.empty()) {
    delete d_usedSets.back();
    d_usedSets.pop_back();
  }

  TNodeMap cache;
  return substitute(e, substTable, cache);
}

