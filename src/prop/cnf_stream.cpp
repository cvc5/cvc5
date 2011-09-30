/*********************                                                        */
/*! \file cnf_stream.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters, dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/

#include "prop/sat.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "theory/theory_engine.h"
#include "expr/node.h"
#include "util/Assert.h"
#include "util/output.h"
#include "expr/command.h"
#include "expr/expr.h"

#include <queue>

using namespace std;
using namespace CVC4::kind;

#ifdef CVC4_REPLAY
#  define CVC4_USE_REPLAY true
#else /* CVC4_REPLAY */
#  define CVC4_USE_REPLAY false
#endif /* CVC4_REPLAY */

namespace CVC4 {
namespace prop {

CnfStream::CnfStream(SatInputInterface *satSolver, theory::Registrar registrar) :
  d_satSolver(satSolver),
  d_registrar(registrar) {
}

void CnfStream::recordTranslation(TNode node) {
  if (!d_removable) {
    d_translationTrail.push_back(stripNot(node));
  }
}

TseitinCnfStream::TseitinCnfStream(SatInputInterface* satSolver, theory::Registrar registrar) :
  CnfStream(satSolver, registrar) {
}

void CnfStream::assertClause(TNode node, SatClause& c) {
  Debug("cnf") << "Inserting into stream " << c << endl;
  if(Dump.isOn("clauses")) {
    if(Message.isOn()) {
      if(c.size() == 1) {
        Message() << AssertCommand(BoolExpr(getNode(c[0]).toExpr())) << endl;
      } else {
        Assert(c.size() > 1);
        NodeBuilder<> b(kind::OR);
        for(int i = 0; i < c.size(); ++i) {
          b << getNode(c[i]);
        }
        Node n = b;
        Message() << AssertCommand(BoolExpr(n.toExpr())) << endl;
      }
    }
  }
  d_satSolver->addClause(c, d_removable);
}

void CnfStream::assertClause(TNode node, SatLiteral a) {
  SatClause clause(1);
  clause[0] = a;
  assertClause(node, clause);
}

void CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b) {
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  assertClause(node, clause);
}

void CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c) {
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  assertClause(node, clause);
}

bool CnfStream::isTranslated(TNode n) const {
  TranslationCache::const_iterator find = d_translationCache.find(n);
  return find != d_translationCache.end() && find->second.level >= 0;
}

bool CnfStream::hasEverHadLiteral(TNode n) const {
  TranslationCache::const_iterator find = d_translationCache.find(n);
  return find != d_translationCache.end();
}

bool CnfStream::currentlyHasLiteral(TNode n) const {
  TranslationCache::const_iterator find = d_translationCache.find(n);
  return find != d_translationCache.end() && (*find).second.level != -1;
}

SatLiteral CnfStream::newLiteral(TNode node, bool theoryLiteral) {
  Debug("cnf") << "newLiteral(" << node << ", " << theoryLiteral << ")" << endl;

  // Get the literal for this node
  SatLiteral lit;
  if (!hasEverHadLiteral(node)) {
    // If no literal, well make one
    lit = variableToLiteral(d_satSolver->newVar(theoryLiteral));
    d_translationCache[node].literal = lit;
    d_translationCache[node.notNode()].literal = ~lit;
  } else {
    // We already have a literal
    lit = getLiteral(node);
    d_satSolver->renewVar(lit);
  }

  // We will translate clauses, so remember the level
  int level = d_satSolver->getLevel();
  d_translationCache[node].level = level;
  d_translationCache[node.notNode()].level = level;

  // If it's a theory literal, need to store it for back queries
  if ( theoryLiteral ||
       ( CVC4_USE_REPLAY && Options::current()->replayLog != NULL ) ||
       Dump.isOn("clauses") ) {
    d_nodeCache[lit] = node;
    d_nodeCache[~lit] = node.notNode();
  }

  // If a theory literal, we pre-register it
  if (theoryLiteral) {
    bool backup = d_removable;
    d_registrar.preRegister(node);
    d_removable = backup;
  }

  // Here, you can have it
  Debug("cnf") << "newLiteral(" << node << ") => " << lit << endl;

  return lit;
}

TNode CnfStream::getNode(const SatLiteral& literal) {
  Debug("cnf") << "getNode(" << literal << ")" << endl;
  NodeCache::iterator find = d_nodeCache.find(literal);
  Assert(find != d_nodeCache.end());
  Assert(d_translationCache.find(find->second) != d_translationCache.end());
  Debug("cnf") << "getNode(" << literal << ") => " << find->second << endl;
  return find->second;
}

SatLiteral CnfStream::convertAtom(TNode node) {
  Debug("cnf") << "convertAtom(" << node << ")" << endl;

  Assert(!isTranslated(node), "atom already mapped!");

  bool theoryLiteral = node.getKind() != kind::VARIABLE && !node.getType().isPseudoboolean();
  SatLiteral lit = newLiteral(node, theoryLiteral);

  if(node.getKind() == kind::CONST_BOOLEAN) {
    if(node.getConst<bool>()) {
      assertClause(node, lit);
    } else {
      assertClause(node, ~lit);
    }
  }

  return lit;
}

SatLiteral CnfStream::getLiteral(TNode node) {
  TranslationCache::iterator find = d_translationCache.find(node);
  Assert(!node.isNull(), "CnfStream: can't getLiteral() of null node");
  Assert(find != d_translationCache.end(), "Literal not in the CNF Cache: %s\n", node.toString().c_str());
  SatLiteral literal = find->second.literal;
  Debug("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal << std::endl;
  return literal;
}

SatLiteral TseitinCnfStream::handleXor(TNode xorNode) {
  Assert(!isTranslated(xorNode), "Atom already mapped!");
  Assert(xorNode.getKind() == XOR, "Expecting an XOR expression!");
  Assert(xorNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  SatLiteral a = toCNF(xorNode[0]);
  SatLiteral b = toCNF(xorNode[1]);

  SatLiteral xorLit = newLiteral(xorNode);

  assertClause(xorNode, a, b, ~xorLit);
  assertClause(xorNode, ~a, ~b, ~xorLit);
  assertClause(xorNode, a, ~b, xorLit);
  assertClause(xorNode, ~a, b, xorLit);

  return xorLit;
}

SatLiteral TseitinCnfStream::handleOr(TNode orNode) {
  Assert(!isTranslated(orNode), "Atom already mapped!");
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
    assertClause(orNode, orLit, ~clause[i]);
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[n_children] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(orNode, clause);

  // Return the literal
  return orLit;
}

SatLiteral TseitinCnfStream::handleAnd(TNode andNode) {
  Assert(!isTranslated(andNode), "Atom already mapped!");
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
    assertClause(andNode, ~andLit, ~clause[i]);
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(andNode, clause);
  return andLit;
}

SatLiteral TseitinCnfStream::handleImplies(TNode impliesNode) {
  Assert(!isTranslated(impliesNode), "Atom already mapped!");
  Assert(impliesNode.getKind() == IMPLIES, "Expecting an IMPLIES expression!");
  Assert(impliesNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  // Convert the children to cnf
  SatLiteral a = toCNF(impliesNode[0]);
  SatLiteral b = toCNF(impliesNode[1]);

  SatLiteral impliesLit = newLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  assertClause(impliesNode, ~impliesLit, ~a, b);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  assertClause(impliesNode, a, impliesLit);
  assertClause(impliesNode, ~b, impliesLit);

  return impliesLit;
}


SatLiteral TseitinCnfStream::handleIff(TNode iffNode) {
  Assert(!isTranslated(iffNode), "Atom already mapped!");
  Assert(iffNode.getKind() == IFF, "Expecting an IFF expression!");
  Assert(iffNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  Debug("cnf") << "handleIff(" << iffNode << ")" << endl;

  // Convert the children to CNF
  SatLiteral a = toCNF(iffNode[0]);
  SatLiteral b = toCNF(iffNode[1]);

  // Get the now literal
  SatLiteral iffLit = newLiteral(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  assertClause(iffNode, ~a, b, ~iffLit);
  assertClause(iffNode, a, ~b, ~iffLit);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  assertClause(iffNode, ~a, ~b, iffLit);
  assertClause(iffNode, a, b, iffLit);

  return iffLit;
}


SatLiteral TseitinCnfStream::handleNot(TNode notNode) {
  Assert(!isTranslated(notNode), "Atom already mapped!");
  Assert(notNode.getKind() == NOT, "Expecting a NOT expression!");
  Assert(notNode.getNumChildren() == 1, "Expecting exactly 1 child!");

  SatLiteral notLit = ~toCNF(notNode[0]);

  return notLit;
}

SatLiteral TseitinCnfStream::handleIte(TNode iteNode) {
  Assert(iteNode.getKind() == ITE);
  Assert(iteNode.getNumChildren() == 3);

  Debug("cnf") << "handleIte(" << iteNode[0] << " " << iteNode[1] << " " << iteNode[2] << ")" << endl;

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
  assertClause(iteNode, ~iteLit, thenLit, elseLit);
  assertClause(iteNode, ~iteLit, ~condLit, thenLit);
  assertClause(iteNode, ~iteLit, condLit, elseLit);

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  assertClause(iteNode, iteLit, ~thenLit, ~elseLit);
  assertClause(iteNode, iteLit, ~condLit, ~thenLit);
  assertClause(iteNode, iteLit, condLit, ~elseLit);

  return iteLit;
}


SatLiteral TseitinCnfStream::toCNF(TNode node, bool negated) {
  Debug("cnf") << "toCNF(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  SatLiteral nodeLit;
  Node negatedNode = node.notNode();

  // If the non-negated node has already been translated, get the translation
  if(isTranslated(node)) {
    nodeLit = getLiteral(node);
  } else {
    // Handle each Boolean operator case
    switch(node.getKind()) {
    case NOT:
      nodeLit = handleNot(node);
      break;
    case XOR:
      nodeLit = handleXor(node);
      break;
    case ITE:
      nodeLit = handleIte(node);
      break;
    case IFF:
      nodeLit = handleIff(node);
      break;
    case IMPLIES:
      nodeLit = handleImplies(node);
      break;
    case OR:
      nodeLit = handleOr(node);
      break;
    case AND:
      nodeLit = handleAnd(node);
      break;
    case EQUAL:
      if(node[0].getType().isBoolean()) {
        // normally this is an IFF, but EQUAL is possible with pseudobooleans
        nodeLit = handleIff(node[0].iffNode(node[1]));
      } else {
        nodeLit = convertAtom(node);
      }
      break;
    default:
      {
        //TODO make sure this does not contain any boolean substructure
        nodeLit = convertAtom(node);
        //Unreachable();
        //Node atomic = handleNonAtomicNode(node);
        //return isCached(atomic) ? lookupInCache(atomic) : convertAtom(atomic);
      }
      break;
    }
  }

  // Return the appropriate (negated) literal
  if (!negated) return nodeLit;
  else return ~nodeLit;
}

void TseitinCnfStream::convertAndAssertAnd(TNode node, bool negated) {
  Assert(node.getKind() == AND);
  if (!negated) {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      convertAndAssert(*conjunct, false);
    }
  } else {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct, true);
      recordTranslation(*disjunct);
    }
    Assert(disjunct == node.end());
    assertClause(node, clause);
  }
}

void TseitinCnfStream::convertAndAssertOr(TNode node, bool negated) {
  Assert(node.getKind() == OR);
  if (!negated) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct, false);
      recordTranslation(*disjunct);
    }
    Assert(disjunct == node.end());
    assertClause(node, clause);
  } else {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      convertAndAssert(*conjunct, true);
    }
  }
}

void TseitinCnfStream::convertAndAssertXor(TNode node, bool negated) {
  if (!negated) {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node, clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node, clause2);
  } else {
    // !(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node, clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node, clause2);
  }
  recordTranslation(node[0]);
  recordTranslation(node[1]);
}

void TseitinCnfStream::convertAndAssertIff(TNode node, bool negated) {
  if (!negated) {
    // p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node, clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node, clause2);
  } else {
    // !(p <=> q) is the same as p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node, clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node, clause2);
  }
  recordTranslation(node[0]);
  recordTranslation(node[1]);
}

void TseitinCnfStream::convertAndAssertImplies(TNode node, bool negated) {
  if (!negated) {
    // p => q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    assertClause(node, clause);
    recordTranslation(node[0]);
    recordTranslation(node[1]);
  } else {// Construct the
    // !(p => q) is the same as (p && ~q)
    convertAndAssert(node[0], false);
    convertAndAssert(node[1], true);
  }
}

void TseitinCnfStream::convertAndAssertIte(TNode node, bool negated) {
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  // Construct the clauses:
  // (p => q) and (!p => r)
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  assertClause(node, clause1);
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  assertClause(node, clause2);

  recordTranslation(node[0]);
  recordTranslation(node[1]);
  recordTranslation(node[2]);
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void TseitinCnfStream::convertAndAssert(TNode node, bool removable, bool negated) {
  Debug("cnf") << "convertAndAssert(" << node << ", removable = " << (removable ? "true" : "false") << ", negated = " << (negated ? "true" : "false") << ")" << endl;
  d_removable = removable;
  convertAndAssert(node, negated);
}

void TseitinCnfStream::convertAndAssert(TNode node, bool negated) {
  Debug("cnf") << "convertAndAssert(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  /*
  if(currentlyHasLiteral(node)) {
    Debug("cnf") << "==> fortunate literal detected!" << endl;
    ++d_fortunateLiterals;
    SatLiteral lit = getLiteral(node);
    //d_satSolver->renewVar(lit);
    assertClause(node, negated ? ~lit : lit);
    return;
  }
  */

  switch(node.getKind()) {
  case AND:
    convertAndAssertAnd(node, negated);
    break;
  case OR:
    convertAndAssertOr(node, negated);
    break;
  case IFF:
    convertAndAssertIff(node, negated);
    break;
  case XOR:
    convertAndAssertXor(node, negated);
    break;
  case IMPLIES:
    convertAndAssertImplies(node, negated);
    break;
  case ITE:
    convertAndAssertIte(node, negated);
    break;
  case NOT:
    convertAndAssert(node[0], !negated);
    break;
  default:
    // Atoms
    assertClause(node, toCNF(node, negated));
    recordTranslation(node);
    break;
  }
}

void CnfStream::removeClausesAboveLevel(int level) {
  while (d_translationTrail.size() > 0) {
    TNode node = d_translationTrail.back();
    Debug("cnf") << "Removing node " << node << " from CNF translation" << endl;
    d_translationTrail.pop_back();
    // Get the translation informations
    TranslationInfo& infoPos = d_translationCache.find(node)->second;
    // If already untranslated, we're done
    if (infoPos.level == -1) continue;
    // If the level of the node is less or equal to given we are done
    if (infoPos.level <= level) break;
    // Otherwise we have to undo the translation
    undoTranslate(node, level);
  }
}

void CnfStream::undoTranslate(TNode node, int level) {
  // Get the translation information
  TranslationInfo& infoPos = d_translationCache.find(node)->second;
  // If already untranslated, we are done
  if (infoPos.level == -1) return;
  // If under the given level we're also done
  if (infoPos.level <= level) return;
  // Untranslate
  infoPos.level = -1;
  // Untranslate the negation node
  // If not a not node, unregister it from sat and untranslate the negation
  if (node.getKind() != kind::NOT) {
    // Unregister the literal from SAT
    SatLiteral lit = getLiteral(node);
    d_satSolver->unregisterVar(lit);
    // Untranslate the negation
    TranslationInfo& infoNeg = d_translationCache.find(node.notNode())->second;
    infoNeg.level = -1;
  }
  // undoTranslate the children
  TNode::iterator child = node.begin();
  TNode::iterator child_end = node.end();
  while (child != child_end) {
    undoTranslate(*child, level);
    ++ child;
  }
}

void CnfStream::moveToBaseLevel(TNode node) {
  TNode posNode = stripNot(node);
  TranslationInfo& infoPos = d_translationCache.find(posNode)->second;

  Assert(infoPos.level >= 0);
  if (infoPos.level == 0) return;

  TNode negNode = node.notNode();
  TranslationInfo& infoNeg = d_translationCache.find(negNode)->second;

  infoPos.level = 0;
  infoNeg.level = 0;

  d_satSolver->renewVar(infoPos.literal, 0);

  // undoTranslate the children
  TNode::iterator child = posNode.begin();
  TNode::iterator child_end = posNode.end();
  while (child != child_end) {
    moveToBaseLevel(*child);
    ++ child;
  }

}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
