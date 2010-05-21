/*********************                                                        */
/** cnf_stream.cpp
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/

#include "sat.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "expr/node.h"
#include "util/Assert.h"
#include "util/output.h"

#include <queue>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace prop {

CnfStream::CnfStream(SatInputInterface *satSolver) :
  d_satSolver(satSolver) {
}

TseitinCnfStream::TseitinCnfStream(SatInputInterface* satSolver) :
  CnfStream(satSolver) {
}

void CnfStream::assertClause(SatClause& c) {
  Debug("cnf") << "Inserting into stream " << c << endl;
  d_satSolver->addClause(c);
}

void CnfStream::assertClause(SatLiteral a) {
  SatClause clause(1);
  clause[0] = a;
  assertClause(clause);
}

void CnfStream::assertClause(SatLiteral a, SatLiteral b) {
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  assertClause(clause);
}

void CnfStream::assertClause(SatLiteral a, SatLiteral b, SatLiteral c) {
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  assertClause(clause);
}

bool CnfStream::isCached(TNode n) const {
  return d_translationCache.find(n) != d_translationCache.end();
}

SatLiteral CnfStream::lookupInCache(TNode n) const {
  Assert(isCached(n), "Node is not in CNF translation cache");
  return d_translationCache.find(n)->second;
}

void CnfStream::cacheTranslation(TNode node, SatLiteral lit) {
  Debug("cnf") << "caching translation " << node << " to " << lit << endl;
  // We always cash bot the node and the negation at the same time
  d_translationCache[node] = lit;
  d_translationCache[node.notNode()] = ~lit;
}

SatLiteral CnfStream::newLiteral(TNode node, bool theoryLiteral) {
  SatLiteral lit = SatLiteral(d_satSolver->newVar(theoryLiteral));
  cacheTranslation(node, lit);
  if (theoryLiteral) {
    d_nodeCache[lit] = node;
    d_nodeCache[~lit] = node.notNode();
  }
  return lit;
}

Node CnfStream::getNode(const SatLiteral& literal) {
  Node node;
  NodeCache::iterator find = d_nodeCache.find(literal);
  if(find != d_nodeCache.end()) {
    node = find->second;
  }
  return node;
}

SatLiteral CnfStream::getLiteral(TNode node) {
  TranslationCache::iterator find = d_translationCache.find(node);
  Assert(find != d_translationCache.end(), "Literal not in the CNF Cache");
  SatLiteral literal = find->second;
  Debug("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal << std::endl;
  return literal;
}

const CnfStream::NodeCache& CnfStream::getNodeCache() const {
  return d_nodeCache;
}

const CnfStream::TranslationCache& CnfStream::getTranslationCache() const {
  return d_translationCache;
}

SatLiteral TseitinCnfStream::handleAtom(TNode node) {
  Assert(node.isAtomic(), "handleAtom(n) expects n to be an atom");
  Assert(!isCached(node), "atom already mapped!");

  Debug("cnf") << "handleAtom(" << node << ")" << endl;
 
  bool theoryLiteral = node.getKind() != kind::VARIABLE;
  SatLiteral lit = newLiteral(node, theoryLiteral);

  if(node.getKind() == kind::CONST_BOOLEAN) {
    if(node.getConst<bool>()) {
      assertClause(lit);
    } else {
      assertClause(~lit);
    }
  }

  return lit;
}

SatLiteral TseitinCnfStream::handleXor(TNode xorNode) {
  Assert(!isCached(xorNode), "Atom already mapped!");
  Assert(xorNode.getKind() == XOR, "Expecting an XOR expression!");
  Assert(xorNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  SatLiteral a = toCNF(xorNode[0]);
  SatLiteral b = toCNF(xorNode[1]);

  SatLiteral xorLit = newLiteral(xorNode);

  assertClause(a, b, ~xorLit);
  assertClause(~a, ~b, ~xorLit);
  assertClause(a, ~b, xorLit);
  assertClause(~a, b, xorLit);

  return xorLit;
}

SatLiteral TseitinCnfStream::handleOr(TNode orNode) {
  Assert(!isCached(orNode), "Atom already mapped!");
  Assert(orNode.getKind() == OR, "Expecting an OR expression!");
  Assert(orNode.getNumChildren() > 1, "Expecting more then 1 child!");

  // Number of children
  unsigned n_children = orNode.getNumChildren();

  // Transform all the children first
  TNode::const_iterator node_it = orNode.begin();
  TNode::const_iterator node_it_end = orNode.end();
  SatClause clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = toCNF(*node_it);
  }

  // Get the literal for this node
  SatLiteral orLit = newLiteral(orNode);

  // lit <- (a_1 | a_2 | a_3 | ... | a_n)
  // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
  // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
  for(unsigned i = 0; i < n_children; ++i) {
    assertClause(orLit, ~clause[i]);
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[n_children] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(clause);

  // Return the literal
  return orLit;
}

SatLiteral TseitinCnfStream::handleAnd(TNode andNode) {
  Assert(!isCached(andNode), "Atom already mapped!");
  Assert(andNode.getKind() == AND, "Expecting an AND expression!");
  Assert(andNode.getNumChildren() > 1, "Expecting more than 1 child!");

  // Number of children
  unsigned n_children = andNode.getNumChildren();

  // Transform all the children first (remembering the negation)
  TNode::const_iterator node_it = andNode.begin();
  TNode::const_iterator node_it_end = andNode.end();
  SatClause clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = ~toCNF(*node_it);
  }

  // Get the literal for this node
  SatLiteral andLit = newLiteral(andNode);

  // lit -> (a_1 & a_2 & a_3 & ... & a_n)
  // ~lit | (a_1 & a_2 & a_3 & ... & a_n)
  // (~lit | a_1) & (~lit | a_2) & ... & (~lit | a_n)
  for(unsigned i = 0; i < n_children; ++i) {
    assertClause(~andLit, ~clause[i]);
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(clause);
  return andLit;
}

SatLiteral TseitinCnfStream::handleImplies(TNode impliesNode) {
  Assert(!isCached(impliesNode), "Atom already mapped!");
  Assert(impliesNode.getKind() == IMPLIES, "Expecting an IMPLIES expression!");
  Assert(impliesNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  // Convert the children to cnf
  SatLiteral a = toCNF(impliesNode[0]);
  SatLiteral b = toCNF(impliesNode[1]);

  SatLiteral impliesLit = newLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  assertClause(~impliesLit, ~a, b);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  assertClause(a, impliesLit);
  assertClause(~b, impliesLit);

  return impliesLit;
}


SatLiteral TseitinCnfStream::handleIff(TNode iffNode) {
  Assert(!isCached(iffNode), "Atom already mapped!");
  Assert(iffNode.getKind() == IFF, "Expecting an IFF expression!");
  Assert(iffNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  // Convert the children to CNF
  SatLiteral a = toCNF(iffNode[0]);
  SatLiteral b = toCNF(iffNode[1]);

  // Get the now literal
  SatLiteral iffLit = newLiteral(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  assertClause(~a, b, ~iffLit);
  assertClause(a, ~b, ~iffLit);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  assertClause(~a, ~b, iffLit);
  assertClause(a, b, iffLit);

  return iffLit;
}


SatLiteral TseitinCnfStream::handleNot(TNode notNode) {
  Assert(!isCached(notNode), "Atom already mapped!");
  Assert(notNode.getKind() == NOT, "Expecting a NOT expression!");
  Assert(notNode.getNumChildren() == 1, "Expecting exactly 1 child!");

  SatLiteral notLit = ~toCNF(notNode[0]);

  // Since we don't introduce new variables, we need to cache the translation
  cacheTranslation(notNode, notLit);

  return notLit;
}

SatLiteral TseitinCnfStream::handleIte(TNode iteNode) {
  Assert(iteNode.getKind() == ITE);
  Assert(iteNode.getNumChildren() == 3);

  Debug("cnf") << "handlIte(" << iteNode[0] << " " << iteNode[1] << " " << iteNode[2] << ")" << endl;

  SatLiteral condLit = toCNF(iteNode[0]);
  SatLiteral thenLit = toCNF(iteNode[1]);
  SatLiteral elseLit = toCNF(iteNode[2]);

  SatLiteral iteLit = newLiteral(iteNode);

  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  assertClause(~iteLit, thenLit, elseLit);
  assertClause(~iteLit, ~condLit, thenLit);
  assertClause(~iteLit, condLit, elseLit);

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  assertClause(iteLit, ~thenLit, ~elseLit);
  assertClause(iteLit, ~condLit, ~thenLit);
  assertClause(iteLit, condLit, ~elseLit);

  return iteLit;
}

Node TseitinCnfStream::handleNonAtomicNode(TNode node) {
  Debug("cnf") << "handleNonAtomicNode(" << node << ")" << endl;

  /* Our main goal here is to tease out any ITE's sitting under a theory operator. */
  Node rewrite;
  NodeManager *nodeManager = NodeManager::currentNM();
  if(nodeManager->getAttribute(node, IteRewriteAttr(), rewrite)) {
    return rewrite.isNull() ? Node(node) : rewrite;
  }

  if(node.getKind() == ITE) {
    Assert( node.getNumChildren() == 3 );
    //TODO should this be a skolem?
    Node skolem = nodeManager->mkVar(node.getType());
    Node newAssertion =
        nodeManager->mkNode(
            ITE,
            node[0],
            nodeManager->mkNode(EQUAL, skolem, node[1]),
            nodeManager->mkNode(EQUAL, skolem, node[2]));
    nodeManager->setAttribute(node, IteRewriteAttr(), skolem);
    convertAndAssert( newAssertion );
    return skolem;
  } else {
    std::vector<Node> newChildren;
    bool somethingChanged = false;
    for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
      Node newChild = handleNonAtomicNode(*it);
      somethingChanged |= (newChild != *it);
      newChildren.push_back(newChild);
    }

    if(somethingChanged) {
      rewrite = nodeManager->mkNode(node.getKind(), newChildren);
      nodeManager->setAttribute(node, IteRewriteAttr(), rewrite);
      return rewrite;
    } else {
      nodeManager->setAttribute(node, IteRewriteAttr(), Node::null());
      return node;
    }
  }
}

SatLiteral TseitinCnfStream::toCNF(TNode node) {
  Debug("cnf") << "toCNF(" << node << ")" << endl;

  // If the node has already been translated, return the previous translation
  if(isCached(node)) {
    return lookupInCache(node);
  }

  // Atomic nodes are treated specially
  if(node.isAtomic()) {
    return handleAtom(node);
  }

  // Handle each Boolean operator case
  switch(node.getKind()) {
  case NOT:
    return handleNot(node);
  case XOR:
    return handleXor(node);
  case ITE:
    return handleIte(node);
  case IFF:
    return handleIff(node);
  case IMPLIES:
    return handleImplies(node);
  case OR:
    return handleOr(node);
  case AND:
    return handleAnd(node);
  default:
    return handleAtom(handleNonAtomicNode(node));
  }
}

void TseitinCnfStream::convertAndAssert(TNode node) {
  Debug("cnf") << "convertAndAssert(" << node << ")" << endl;
  if(node.getKind() == AND) {
    // If the node is a conjunction, we handle each conjunct separately
    for( TNode::const_iterator conjunct = node.begin(),
         node_end = node.end();
         conjunct != node_end;
         ++conjunct ) {
      convertAndAssert(*conjunct);
    }
  } else if(node.getKind() == OR) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct);
    }
    Assert( disjunct == node.end() );
    assertClause(clause);
  } else {
    // Otherwise, we just convert using the definitional transformation
    assertClause(toCNF(node));
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
