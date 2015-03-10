/*********************                                                        */
/*! \file cnf_stream.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters, Dejan Jovanovic
 ** Minor contributors (to current version): Kshitij Bansal, Liana Hadarean, Christopher L. Conway, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory.h"
#include "expr/node.h"
#include "util/cvc4_assert.h"
#include "util/output.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "prop/theory_proxy.h"
#include "theory/bv/options.h"
#include "proof/proof_manager.h"
#include "proof/sat_proof.h"
#include "prop/minisat/minisat.h"
#include "smt/smt_engine_scope.h"
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

CnfStream::CnfStream(SatSolver *satSolver, Registrar* registrar, context::Context* context, bool fullLitToNodeMap) :
  d_satSolver(satSolver),
  d_booleanVariables(context),
  d_nodeToLiteralMap(context),
  d_literalToNodeMap(context),
  d_fullLitToNodeMap(fullLitToNodeMap),
  d_convertAndAssertCounter(0),
  d_registrar(registrar),
  d_assertionTable(context),
  d_removable(false) {
}

TseitinCnfStream::TseitinCnfStream(SatSolver* satSolver, Registrar* registrar, context::Context* context, bool fullLitToNodeMap) :
  CnfStream(satSolver, registrar, context, fullLitToNodeMap) {
}

void CnfStream::assertClause(TNode node, SatClause& c, ProofRule proof_id) {
  Debug("cnf") << "Inserting into stream " << c << " node = " << node << ", proof id = " << proof_id << endl;
  if(Dump.isOn("clauses")) {
    if(c.size() == 1) {
      Dump("clauses") << AssertCommand(Expr(getNode(c[0]).toExpr()));
    } else {
      Assert(c.size() > 1);
      NodeBuilder<> b(kind::OR);
      for(unsigned i = 0; i < c.size(); ++i) {
        b << getNode(c[i]);
      }
      Node n = b;
      Dump("clauses") << AssertCommand(Expr(n.toExpr()));
    }
  }
  //store map between clause and original formula
  PROOF(ProofManager::currentPM()->setRegisteringFormula( node, proof_id ); );
  d_satSolver->addClause(c, d_removable, d_proofId);
  PROOF(ProofManager::currentPM()->setRegisteringFormula( Node::null(), RULE_INVALID ); );
}

void CnfStream::assertClause(TNode node, SatLiteral a, ProofRule proof_id) {
  SatClause clause(1);
  clause[0] = a;
  assertClause(node, clause, proof_id);
}

void CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b, ProofRule proof_id) {
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  assertClause(node, clause, proof_id);
}

void CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c, ProofRule proof_id) {
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  assertClause(node, clause, proof_id);
}

bool CnfStream::hasLiteral(TNode n) const {
  NodeToLiteralMap::const_iterator find = d_nodeToLiteralMap.find(n);
  return find != d_nodeToLiteralMap.end();
}

void TseitinCnfStream::ensureLiteral(TNode n) {
  // These are not removable and have no proof ID
  d_removable = false;
  d_proofId = uint64_t(-1);

  Debug("cnf") << "ensureLiteral(" << n << ")" << endl;
  if(hasLiteral(n)) {
    SatLiteral lit = getLiteral(n);
    if(!d_literalToNodeMap.contains(lit)){
      // Store backward-mappings
      d_literalToNodeMap.insert(lit, n);
      d_literalToNodeMap.insert(~lit, n.notNode());
    }
    return;
  }

  AlwaysAssertArgument(n.getType().isBoolean(), n,
                       "CnfStream::ensureLiteral() requires a node of Boolean type.\n"
                       "got node: %s\n"
                       "its type: %s\n",
                       n.toString().c_str(),
                       n.getType().toString().c_str());

  bool negated CVC4_UNUSED = false;
  SatLiteral lit;

  if(n.getKind() == kind::NOT) {
    negated = true;
    n = n[0];
  }

  if( theory::Theory::theoryOf(n) == theory::THEORY_BOOL &&
      !n.isVar() ) {
    // If we were called with something other than a theory atom (or
    // Boolean variable), we get a SatLiteral that is definitionally
    // equal to it.
    lit = toCNF(n, false);

    // Store backward-mappings
    // These may already exist
    d_literalToNodeMap.insert_safe(lit, n);
    d_literalToNodeMap.insert_safe(~lit, n.notNode());
  } else {
    // We have a theory atom or variable.
    lit = convertAtom(n);
  }

  Assert(hasLiteral(n) && getNode(lit) == n);
  Debug("ensureLiteral") << "CnfStream::ensureLiteral(): out lit is " << lit << std::endl;
}

SatLiteral CnfStream::newLiteral(TNode node, bool isTheoryAtom, bool preRegister, bool canEliminate) {
  Debug("cnf") << "newLiteral(" << node << ", " << isTheoryAtom << ")" << endl;
  Assert(node.getKind() != kind::NOT);

  // Get the literal for this node
  SatLiteral lit;
  if (!hasLiteral(node)) {
    // If no literal, we'll make one
    if (node.getKind() == kind::CONST_BOOLEAN) {
      if (node.getConst<bool>()) {
        lit = SatLiteral(d_satSolver->trueVar());
      } else {
        lit = SatLiteral(d_satSolver->falseVar());
      }
    } else {
      lit = SatLiteral(d_satSolver->newVar(isTheoryAtom, preRegister, canEliminate));
    }
    d_nodeToLiteralMap.insert(node, lit);
    d_nodeToLiteralMap.insert(node.notNode(), ~lit);
  } else {
    lit = getLiteral(node);
  }

  // If it's a theory literal, need to store it for back queries
  if ( isTheoryAtom || d_fullLitToNodeMap ||
       ( CVC4_USE_REPLAY && options::replayLog() != NULL ) ||
       (Dump.isOn("clauses")) ) {

    d_literalToNodeMap.insert_safe(lit, node);
    d_literalToNodeMap.insert_safe(~lit, node.notNode());
  }

  // If a theory literal, we pre-register it
  if (preRegister) {
    // In case we are re-entered due to lemmas, save our state
    bool backupRemovable = d_removable;
    uint64_t backupProofId= d_proofId;
    d_registrar->preRegister(node);
    d_removable = backupRemovable;
    d_proofId = backupProofId;
  }

  // Here, you can have it
  Debug("cnf") << "newLiteral(" << node << ") => " << lit << endl;

  return lit;
}

TNode CnfStream::getNode(const SatLiteral& literal) {
  Debug("cnf") << "getNode(" << literal << ")" << endl;
  Debug("cnf") << "getNode(" << literal << ") => " << d_literalToNodeMap[literal] << endl;
  return d_literalToNodeMap[literal];
}

void CnfStream::getBooleanVariables(std::vector<TNode>& outputVariables) const {
  context::CDList<TNode>::const_iterator it, it_end;
  for (it = d_booleanVariables.begin(); it != d_booleanVariables.end(); ++ it) {
    outputVariables.push_back(*it);
  }
}

SatLiteral CnfStream::convertAtom(TNode node) {
  Debug("cnf") << "convertAtom(" << node << ")" << endl;

  Assert(!hasLiteral(node), "atom already mapped!");

  bool theoryLiteral = false;
  bool canEliminate = true;
  bool preRegister = false;

  // Is this a variable add it to the list
  if (node.isVar()) {
    d_booleanVariables.push_back(node);
  } else {
    theoryLiteral = true;
    canEliminate = false;
    preRegister = true;
  }

  // Make a new literal (variables are not considered theory literals)
  SatLiteral lit = newLiteral(node, theoryLiteral, preRegister, canEliminate);
  // Return the resulting literal
  return lit;
}

SatLiteral CnfStream::getLiteral(TNode node) {
  Assert(!node.isNull(), "CnfStream: can't getLiteral() of null node");
  Assert(d_nodeToLiteralMap.contains(node), "Literal not in the CNF Cache: %s\n", node.toString().c_str());
  SatLiteral literal = d_nodeToLiteralMap[node];
  Debug("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal << std::endl;
  return literal;
}

SatLiteral TseitinCnfStream::handleXor(TNode xorNode) {
  Assert(!hasLiteral(xorNode), "Atom already mapped!");
  Assert(xorNode.getKind() == XOR, "Expecting an XOR expression!");
  Assert(xorNode.getNumChildren() == 2, "Expecting exactly 2 children!");
  Assert(!d_removable, "Removable clauses can not contain Boolean structure");

  SatLiteral a = toCNF(xorNode[0]);
  SatLiteral b = toCNF(xorNode[1]);

  SatLiteral xorLit = newLiteral(xorNode);

  assertClause(xorNode.negate(), a, b, ~xorLit, RULE_TSEITIN);
  assertClause(xorNode.negate(), ~a, ~b, ~xorLit, RULE_TSEITIN);
  assertClause(xorNode, a, ~b, xorLit, RULE_TSEITIN);
  assertClause(xorNode, ~a, b, xorLit, RULE_TSEITIN);

  return xorLit;
}

SatLiteral TseitinCnfStream::handleOr(TNode orNode) {
  Assert(!hasLiteral(orNode), "Atom already mapped!");
  Assert(orNode.getKind() == OR, "Expecting an OR expression!");
  Assert(orNode.getNumChildren() > 1, "Expecting more then 1 child!");
  Assert(!d_removable, "Removable clauses can not contain Boolean structure");

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
    assertClause(orNode, orLit, ~clause[i], RULE_TSEITIN);
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[n_children] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(orNode.negate(), clause, RULE_TSEITIN);

  // Return the literal
  return orLit;
}

SatLiteral TseitinCnfStream::handleAnd(TNode andNode) {
  Assert(!hasLiteral(andNode), "Atom already mapped!");
  Assert(andNode.getKind() == AND, "Expecting an AND expression!");
  Assert(andNode.getNumChildren() > 1, "Expecting more than 1 child!");
  Assert(!d_removable, "Removable clauses can not contain Boolean structure");

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
    assertClause(andNode.negate(), ~andLit, ~clause[i], RULE_TSEITIN);
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(andNode, clause, RULE_TSEITIN);

  return andLit;
}

SatLiteral TseitinCnfStream::handleImplies(TNode impliesNode) {
  Assert(!hasLiteral(impliesNode), "Atom already mapped!");
  Assert(impliesNode.getKind() == IMPLIES, "Expecting an IMPLIES expression!");
  Assert(impliesNode.getNumChildren() == 2, "Expecting exactly 2 children!");
  Assert(!d_removable, "Removable clauses can not contain Boolean structure");

  // Convert the children to cnf
  SatLiteral a = toCNF(impliesNode[0]);
  SatLiteral b = toCNF(impliesNode[1]);

  SatLiteral impliesLit = newLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  assertClause(impliesNode.negate(), ~impliesLit, ~a, b, RULE_TSEITIN);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  assertClause(impliesNode, a, impliesLit, RULE_TSEITIN);
  assertClause(impliesNode, ~b, impliesLit, RULE_TSEITIN);

  return impliesLit;
}


SatLiteral TseitinCnfStream::handleIff(TNode iffNode) {
  Assert(!hasLiteral(iffNode), "Atom already mapped!");
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
  assertClause(iffNode.negate(), ~a, b, ~iffLit, RULE_TSEITIN);
  assertClause(iffNode.negate(), a, ~b, ~iffLit, RULE_TSEITIN);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  assertClause(iffNode, ~a, ~b, iffLit, RULE_TSEITIN);
  assertClause(iffNode, a, b, iffLit, RULE_TSEITIN);

  return iffLit;
}


SatLiteral TseitinCnfStream::handleNot(TNode notNode) {
  Assert(!hasLiteral(notNode), "Atom already mapped!");
  Assert(notNode.getKind() == NOT, "Expecting a NOT expression!");
  Assert(notNode.getNumChildren() == 1, "Expecting exactly 1 child!");

  SatLiteral notLit = ~toCNF(notNode[0]);

  return notLit;
}

SatLiteral TseitinCnfStream::handleIte(TNode iteNode) {
  Assert(iteNode.getKind() == ITE);
  Assert(iteNode.getNumChildren() == 3);
  Assert(!d_removable, "Removable clauses can not contain Boolean structure");

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
  assertClause(iteNode.negate(), ~iteLit, thenLit, elseLit, RULE_TSEITIN);
  assertClause(iteNode.negate(), ~iteLit, ~condLit, thenLit, RULE_TSEITIN);
  assertClause(iteNode.negate(), ~iteLit, condLit, elseLit, RULE_TSEITIN);

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  assertClause(iteNode, iteLit, ~thenLit, ~elseLit, RULE_TSEITIN);
  assertClause(iteNode, iteLit, ~condLit, ~thenLit, RULE_TSEITIN);
  assertClause(iteNode, iteLit, condLit, ~elseLit, RULE_TSEITIN);

  return iteLit;
}


SatLiteral TseitinCnfStream::toCNF(TNode node, bool negated) {
  Debug("cnf") << "toCNF(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  SatLiteral nodeLit;
  Node negatedNode = node.notNode();

  // If the non-negated node has already been translated, get the translation
  if(hasLiteral(node)) {
    Debug("cnf") << "toCNF(): already translated" << endl;
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

void TseitinCnfStream::convertAndAssertAnd(TNode node, bool negated, ProofRule proof_id) {
  Assert(node.getKind() == AND);
  if (!negated) {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      PROOF(ProofManager::currentPM()->setCnfDep( (*conjunct).toExpr(), node.toExpr() ) );
      convertAndAssert(*conjunct, false, proof_id);
    }
  } else {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct, true);
    }
    Assert(disjunct == node.end());
    assertClause(node.negate(), clause, proof_id);
  }
}

void TseitinCnfStream::convertAndAssertOr(TNode node, bool negated, ProofRule proof_id) {
  Assert(node.getKind() == OR);
  if (!negated) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCNF(*disjunct, false);
    }
    Assert(disjunct == node.end());
    assertClause(node, clause, proof_id);
  } else {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      PROOF(ProofManager::currentPM()->setCnfDep( (*conjunct).negate().toExpr(), node.negate().toExpr() ) );
      convertAndAssert(*conjunct, true, proof_id);
    }
  }
}

void TseitinCnfStream::convertAndAssertXor(TNode node, bool negated, ProofRule proof_id) {
  if (!negated) {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node, clause1, proof_id);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node, clause2, proof_id);
  } else {
    // !(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node.negate(), clause1, proof_id);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node.negate(), clause2, proof_id);
  }
}

void TseitinCnfStream::convertAndAssertIff(TNode node, bool negated, ProofRule proof_id) {
  if (!negated) {
    // p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node, clause1, proof_id);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node, clause2, proof_id);
  } else {
    // !(p <=> q) is the same as p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node.negate(), clause1, proof_id);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node.negate(), clause2, proof_id);
  }
}

void TseitinCnfStream::convertAndAssertImplies(TNode node, bool negated, ProofRule proof_id) {
  if (!negated) {
    // p => q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    assertClause(node, clause, proof_id);
  } else {// Construct the
    PROOF(ProofManager::currentPM()->setCnfDep( node[0].toExpr(), node.negate().toExpr() ) );
    PROOF(ProofManager::currentPM()->setCnfDep( node[1].negate().toExpr(), node.negate().toExpr() ) );
    // !(p => q) is the same as (p && ~q)
    convertAndAssert(node[0], false, proof_id);
    convertAndAssert(node[1], true, proof_id);
  }
}

void TseitinCnfStream::convertAndAssertIte(TNode node, bool negated, ProofRule proof_id) {
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  // Construct the clauses:
  // (p => q) and (!p => r)
  Node nnode = node;
  if( negated ){
    nnode = node.negate();
  }
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  assertClause(nnode, clause1, proof_id);
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  assertClause(nnode, clause2, proof_id);
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void TseitinCnfStream::convertAndAssert(TNode node, bool removable, bool negated, ProofRule proof_id, TNode from) {
  Debug("cnf") << "convertAndAssert(" << node << ", removable = " << (removable ? "true" : "false") << ", negated = " << (negated ? "true" : "false") << ")" << endl;
  d_removable = removable;
  if(options::proof() || options::unsatCores()) {
    // Encode the assertion ID in the proof_id to store with generated clauses.
    uint64_t assertionTableIndex = d_assertionTable.size();
    Assert((uint64_t(proof_id) & 0xffffffff00000000llu) == 0 && (assertionTableIndex & 0xffffffff00000000llu) == 0, "proof_id/table_index collision");
    d_proofId = assertionTableIndex | (uint64_t(proof_id) << 32);
    d_assertionTable.push_back(from.isNull() ? node : from);
    Debug("cores") << "cnf ix " << assertionTableIndex << " asst " << node << "  proof_id " << proof_id << " from " << from << endl;
  } else {
    // We aren't producing proofs or unsat cores; use an invalid proof id.
    d_proofId = uint64_t(-1);
  }
  convertAndAssert(node, negated, proof_id);
}

void TseitinCnfStream::convertAndAssert(TNode node, bool negated, ProofRule proof_id) {
  Debug("cnf") << "convertAndAssert(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  if (d_convertAndAssertCounter % ResourceManager::getFrequencyCount() == 0) {
    NodeManager::currentResourceManager()->spendResource();
    d_convertAndAssertCounter = 0;
  }
  ++d_convertAndAssertCounter;

  switch(node.getKind()) {
  case AND:
    convertAndAssertAnd(node, negated, proof_id);
    break;
  case OR:
    convertAndAssertOr(node, negated, proof_id);
    break;
  case IFF:
    convertAndAssertIff(node, negated, proof_id);
    break;
  case XOR:
    convertAndAssertXor(node, negated, proof_id);
    break;
  case IMPLIES:
    convertAndAssertImplies(node, negated, proof_id);
    break;
  case ITE:
    convertAndAssertIte(node, negated, proof_id);
    break;
  case NOT:
    convertAndAssert(node[0], !negated, proof_id);
    break;
  default:
  {
    Node nnode = node;
    if( negated ){
      nnode = node.negate();
    }
    // Atoms
    assertClause(nnode, toCNF(node, negated), proof_id);
  }
    break;
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
