/*********************                                                        */
/*! \file cnf_stream.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/
#include "prop/cnf_stream.h"

#include <queue>

#include "base/check.h"
#include "base/output.h"
#include "expr/expr.h"
#include "expr/node.h"
#include "options/bv_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/proof_manager.h"
#include "proof/sat_proof.h"
#include "prop/minisat/minisat.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "smt/dump.h"
#include "smt/smt_engine.h"
#include "printer/printer.h"
#include "smt/smt_engine_scope.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace prop {

CnfStream::CnfStream(SatSolver* satSolver,
                     Registrar* registrar,
                     context::Context* context,
                     OutputManager* outMgr,
                     ResourceManager* rm,
                     bool fullLitToNodeMap,
                     std::string name)
    : d_satSolver(satSolver),
      d_outMgr(outMgr),
      d_booleanVariables(context),
      d_nodeToLiteralMap(context),
      d_literalToNodeMap(context),
      d_fullLitToNodeMap(fullLitToNodeMap),
      d_convertAndAssertCounter(0),
      d_registrar(registrar),
      d_name(name),
      d_cnfProof(nullptr),
      d_removable(false),
      d_resourceManager(rm)
{
}

bool CnfStream::assertClause(TNode node, SatClause& c)
{
  Trace("cnf") << "Inserting into stream " << c << " node = " << node << "\n";
  if (Dump.isOn("clauses") && d_outMgr != nullptr)
  {
    const Printer& printer = d_outMgr->getPrinter();
    std::ostream& out = d_outMgr->getDumpOut();
    if (c.size() == 1)
    {
      printer.toStreamCmdAssert(out, getNode(c[0]));
    }
    else
    {
      Assert(c.size() > 1);
      NodeBuilder<> b(kind::OR);
      for (unsigned i = 0; i < c.size(); ++i)
      {
        b << getNode(c[i]);
      }
      Node n = b;
      printer.toStreamCmdAssert(out, n);
    }
  }

  ClauseId clauseId = d_satSolver->addClause(c, d_removable);

  if (d_cnfProof && clauseId != ClauseIdUndef)
  {
    d_cnfProof->registerConvertedClause(clauseId);
  }
  return clauseId != ClauseIdUndef;
}

bool CnfStream::assertClause(TNode node, SatLiteral a)
{
  SatClause clause(1);
  clause[0] = a;
  return assertClause(node, clause);
}

bool CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b)
{
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  return assertClause(node, clause);
}

bool CnfStream::assertClause(TNode node,
                             SatLiteral a,
                             SatLiteral b,
                             SatLiteral c)
{
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  return assertClause(node, clause);
}

bool CnfStream::hasLiteral(TNode n) const {
  NodeToLiteralMap::const_iterator find = d_nodeToLiteralMap.find(n);
  return find != d_nodeToLiteralMap.end();
}

void CnfStream::ensureLiteral(TNode n, bool noPreregistration)
{
  // These are not removable and have no proof ID
  d_removable = false;

  Trace("cnf") << "ensureLiteral(" << n << ")\n";
  if(hasLiteral(n)) {
    SatLiteral lit = getLiteral(n);
    if(!d_literalToNodeMap.contains(lit)){
      // Store backward-mappings
      d_literalToNodeMap.insert(lit, n);
      d_literalToNodeMap.insert(~lit, n.notNode());
    }
    return;
  }

  AlwaysAssertArgument(
      n.getType().isBoolean(),
      n,
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
    //
    // We are setting the current assertion to be null. This is because `toCNF`
    // may add clauses to the SAT solver and we look up the current assertion
    // in that case. Setting it to null ensures that the assertion stack is
    // non-empty and that we are not associating a bogus assertion with the
    // clause. This should be ok because we use the mapping back to assertions
    // for clauses from input assertions only.
    if (d_cnfProof)
    {
      d_cnfProof->pushCurrentAssertion(Node::null());
    }

    lit = toCNF(n, false);

    if (d_cnfProof)
    {
      d_cnfProof->popCurrentAssertion();
    }

    // Store backward-mappings
    // These may already exist
    d_literalToNodeMap.insert_safe(lit, n);
    d_literalToNodeMap.insert_safe(~lit, n.notNode());
  } else {
    // We have a theory atom or variable.
    lit = convertAtom(n, noPreregistration);
  }

  Assert(hasLiteral(n) && getNode(lit) == n);
  Debug("ensureLiteral") << "CnfStream::ensureLiteral(): out lit is " << lit << std::endl;
}

SatLiteral CnfStream::newLiteral(TNode node, bool isTheoryAtom, bool preRegister, bool canEliminate) {
  Trace("cnf") << d_name << "::newLiteral(" << node << ", " << isTheoryAtom
               << ")\n"
               << push;
  Assert(node.getKind() != kind::NOT);

  // Get the literal for this node
  SatLiteral lit;
  if (!hasLiteral(node)) {
    Trace("cnf") << d_name << "::newLiteral: node already registered\n";
    // If no literal, we'll make one
    if (node.getKind() == kind::CONST_BOOLEAN) {
      Trace("cnf") << d_name << "::newLiteral: boolean const\n";
      if (node.getConst<bool>()) {
        lit = SatLiteral(d_satSolver->trueVar());
      } else {
        lit = SatLiteral(d_satSolver->falseVar());
      }
    } else {
      Trace("cnf") << d_name << "::newLiteral: new var\n";
      lit = SatLiteral(d_satSolver->newVar(isTheoryAtom, preRegister, canEliminate));
    }
    d_nodeToLiteralMap.insert(node, lit);
    d_nodeToLiteralMap.insert(node.notNode(), ~lit);
  } else {
    lit = getLiteral(node);
  }

  // If it's a theory literal, need to store it for back queries
  if ( isTheoryAtom || d_fullLitToNodeMap || (Dump.isOn("clauses")) ) {
    d_literalToNodeMap.insert_safe(lit, node);
    d_literalToNodeMap.insert_safe(~lit, node.notNode());
  }

  // If a theory literal, we pre-register it
  if (preRegister) {
    // In case we are re-entered due to lemmas, save our state
    bool backupRemovable = d_removable;
    // Should be fine since cnfProof current assertion is stack based.
    d_registrar->preRegister(node);
    d_removable = backupRemovable;
  }
  // Here, you can have it
  Trace("cnf") << "newLiteral(" << node << ") => " << lit << "\n" << pop;
  return lit;
}

TNode CnfStream::getNode(const SatLiteral& literal) {
  Trace("cnf") << "getNode(" << literal << ")\n";
  Trace("cnf") << "getNode(" << literal << ") => "
               << d_literalToNodeMap[literal] << "\n";
  return d_literalToNodeMap[literal];
}

const CnfStream::NodeToLiteralMap& CnfStream::getTranslationCache() const
{
  return d_nodeToLiteralMap;
}

const CnfStream::LiteralToNodeMap& CnfStream::getNodeCache() const
{
  return d_literalToNodeMap;
}

void CnfStream::getBooleanVariables(std::vector<TNode>& outputVariables) const {
  context::CDList<TNode>::const_iterator it, it_end;
  for (it = d_booleanVariables.begin(); it != d_booleanVariables.end(); ++ it) {
    outputVariables.push_back(*it);
  }
}

void CnfStream::setProof(CnfProof* proof) {
  Assert(d_cnfProof == NULL);
  d_cnfProof = proof;
}

SatLiteral CnfStream::convertAtom(TNode node, bool noPreregistration) {
  Trace("cnf") << "convertAtom(" << node << ")\n";

  Assert(!hasLiteral(node)) << "atom already mapped!";

  bool theoryLiteral = false;
  bool canEliminate = true;
  bool preRegister = false;

  // Is this a variable add it to the list
  if (node.isVar() && node.getKind() != kind::BOOLEAN_TERM_VARIABLE)
  {
    d_booleanVariables.push_back(node);
  }
  else
  {
    theoryLiteral = true;
    canEliminate = false;
    preRegister = !noPreregistration;
  }

  // Make a new literal (variables are not considered theory literals)
  SatLiteral lit = newLiteral(node, theoryLiteral, preRegister, canEliminate);
  // Return the resulting literal
  return lit;
}

SatLiteral CnfStream::getLiteral(TNode node) {
  Assert(!node.isNull()) << "CnfStream: can't getLiteral() of null node";

  Assert(d_nodeToLiteralMap.contains(node))
      << "Literal not in the CNF Cache: " << node << "\n";

  SatLiteral literal = d_nodeToLiteralMap[node];
  Trace("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal
               << "\n";
  return literal;
}

SatLiteral CnfStream::handleXor(TNode xorNode)
{
  Assert(!hasLiteral(xorNode)) << "Atom already mapped!";
  Assert(xorNode.getKind() == kind::XOR) << "Expecting an XOR expression!";
  Assert(xorNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "CnfStream::handleXor(" << xorNode << ")\n";

  SatLiteral a = toCNF(xorNode[0]);
  SatLiteral b = toCNF(xorNode[1]);

  SatLiteral xorLit = newLiteral(xorNode);

  assertClause(xorNode.negate(), a, b, ~xorLit);
  assertClause(xorNode.negate(), ~a, ~b, ~xorLit);
  assertClause(xorNode, a, ~b, xorLit);
  assertClause(xorNode, ~a, b, xorLit);

  return xorLit;
}

SatLiteral CnfStream::handleOr(TNode orNode)
{
  Assert(!hasLiteral(orNode)) << "Atom already mapped!";
  Assert(orNode.getKind() == kind::OR) << "Expecting an OR expression!";
  Assert(orNode.getNumChildren() > 1) << "Expecting more then 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "CnfStream::handleOr(" << orNode << ")\n";

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
  assertClause(orNode.negate(), clause);

  // Return the literal
  return orLit;
}

SatLiteral CnfStream::handleAnd(TNode andNode)
{
  Assert(!hasLiteral(andNode)) << "Atom already mapped!";
  Assert(andNode.getKind() == kind::AND) << "Expecting an AND expression!";
  Assert(andNode.getNumChildren() > 1) << "Expecting more than 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleAnd(" << andNode << ")\n";

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
    assertClause(andNode.negate(), ~andLit, ~clause[i]);
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(andNode, clause);

  return andLit;
}

SatLiteral CnfStream::handleImplies(TNode impliesNode)
{
  Assert(!hasLiteral(impliesNode)) << "Atom already mapped!";
  Assert(impliesNode.getKind() == kind::IMPLIES)
      << "Expecting an IMPLIES expression!";
  Assert(impliesNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleImplies(" << impliesNode << ")\n";

  // Convert the children to cnf
  SatLiteral a = toCNF(impliesNode[0]);
  SatLiteral b = toCNF(impliesNode[1]);

  SatLiteral impliesLit = newLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  assertClause(impliesNode.negate(), ~impliesLit, ~a, b);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  assertClause(impliesNode, a, impliesLit);
  assertClause(impliesNode, ~b, impliesLit);

  return impliesLit;
}

SatLiteral CnfStream::handleIff(TNode iffNode)
{
  Assert(!hasLiteral(iffNode)) << "Atom already mapped!";
  Assert(iffNode.getKind() == kind::EQUAL) << "Expecting an EQUAL expression!";
  Assert(iffNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleIff(" << iffNode << ")\n";

  // Convert the children to CNF
  SatLiteral a = toCNF(iffNode[0]);
  SatLiteral b = toCNF(iffNode[1]);

  // Get the now literal
  SatLiteral iffLit = newLiteral(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  assertClause(iffNode.negate(), ~a, b, ~iffLit);
  assertClause(iffNode.negate(), a, ~b, ~iffLit);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  assertClause(iffNode, ~a, ~b, iffLit);
  assertClause(iffNode, a, b, iffLit);

  return iffLit;
}

SatLiteral CnfStream::handleIte(TNode iteNode)
{
  Assert(!hasLiteral(iteNode)) << "Atom already mapped!";
  Assert(iteNode.getKind() == kind::ITE);
  Assert(iteNode.getNumChildren() == 3);
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleIte(" << iteNode[0] << " " << iteNode[1] << " "
               << iteNode[2] << ")\n";

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
  assertClause(iteNode.negate(), ~iteLit, thenLit, elseLit);
  assertClause(iteNode.negate(), ~iteLit, ~condLit, thenLit);
  assertClause(iteNode.negate(), ~iteLit, condLit, elseLit);

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

SatLiteral CnfStream::toCNF(TNode node, bool negated)
{
  Trace("cnf") << "toCNF(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  SatLiteral nodeLit;
  Node negatedNode = node.notNode();

  // If the non-negated node has already been translated, get the translation
  if(hasLiteral(node)) {
    Trace("cnf") << "toCNF(): already translated\n";
    nodeLit = getLiteral(node);
    // Return the (maybe negated) literal
    return !negated ? nodeLit : ~nodeLit;
  }
  // Handle each Boolean operator case
  switch (node.getKind())
  {
    case kind::NOT: nodeLit = ~toCNF(node[0]); break;
    case kind::XOR: nodeLit = handleXor(node); break;
    case kind::ITE: nodeLit = handleIte(node); break;
    case kind::IMPLIES: nodeLit = handleImplies(node); break;
    case kind::OR: nodeLit = handleOr(node); break;
    case kind::AND: nodeLit = handleAnd(node); break;
    case kind::EQUAL:
      nodeLit =
          node[0].getType().isBoolean() ? handleIff(node) : convertAtom(node);
      break;
    default:
    {
      nodeLit = convertAtom(node);
    }
    break;
  }
  // Return the (maybe negated) literal
  return !negated ? nodeLit : ~nodeLit;
}

void CnfStream::convertAndAssertAnd(TNode node, bool negated)
{
  Assert(node.getKind() == kind::AND);
  Trace("cnf") << "CnfStream::convertAndAssertAnd(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
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
      Assert(disjunct != node.end());
      clause[i] = toCNF(*disjunct, true);
    }
    Assert(disjunct == node.end());
    assertClause(node.negate(), clause);
  }
}

void CnfStream::convertAndAssertOr(TNode node, bool negated)
{
  Assert(node.getKind() == kind::OR);
  Trace("cnf") << "CnfStream::convertAndAssertOr(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  if (!negated) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert(disjunct != node.end());
      clause[i] = toCNF(*disjunct, false);
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

void CnfStream::convertAndAssertXor(TNode node, bool negated)
{
  Assert(node.getKind() == kind::XOR);
  Trace("cnf") << "CnfStream::convertAndAssertXor(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
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
    assertClause(node.negate(), clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node.negate(), clause2);
  }
}

void CnfStream::convertAndAssertIff(TNode node, bool negated)
{
  Assert(node.getKind() == kind::EQUAL);
  Trace("cnf") << "CnfStream::convertAndAssertIff(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
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
    assertClause(node.negate(), clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node.negate(), clause2);
  }
}

void CnfStream::convertAndAssertImplies(TNode node, bool negated)
{
  Assert(node.getKind() == kind::IMPLIES);
  Trace("cnf") << "CnfStream::convertAndAssertImplies(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  if (!negated) {
    // p => q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    assertClause(node, clause);
  } else {// Construct the
    // !(p => q) is the same as (p && ~q)
    convertAndAssert(node[0], false);
    convertAndAssert(node[1], true);
  }
}

void CnfStream::convertAndAssertIte(TNode node, bool negated)
{
  Assert(node.getKind() == kind::ITE);
  Trace("cnf") << "CnfStream::convertAndAssertIte(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  // Construct the clauses:
  // (p => q) and (!p => r)
  //
  // Note that below q and r can be used directly because whether they are
  // negated has been push to the literal definitions above
  Node nnode = node;
  if( negated ){
    nnode = node.negate();
  }
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  assertClause(nnode, clause1);
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  assertClause(nnode, clause2);
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void CnfStream::convertAndAssert(TNode node,
                                 bool removable,
                                 bool negated,
                                 bool input)
{
  Trace("cnf") << "convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", removable = " << (removable ? "true" : "false") << ")\n";
  d_removable = removable;

  if (d_cnfProof)
  {
    d_cnfProof->pushCurrentAssertion(negated ? node.notNode() : (Node)node,
                                     input);
  }
  convertAndAssert(node, negated);
  if (d_cnfProof)
  {
    d_cnfProof->popCurrentAssertion();
  }
}

void CnfStream::convertAndAssert(TNode node, bool negated)
{
  Trace("cnf") << "convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";

  if (d_convertAndAssertCounter % ResourceManager::getFrequencyCount() == 0) {
    d_resourceManager->spendResource(ResourceManager::Resource::CnfStep);
    d_convertAndAssertCounter = 0;
  }
  ++d_convertAndAssertCounter;

  switch(node.getKind()) {
    case kind::AND: convertAndAssertAnd(node, negated); break;
    case kind::OR: convertAndAssertOr(node, negated); break;
    case kind::XOR: convertAndAssertXor(node, negated); break;
    case kind::IMPLIES: convertAndAssertImplies(node, negated); break;
    case kind::ITE: convertAndAssertIte(node, negated); break;
    case kind::NOT: convertAndAssert(node[0], !negated); break;
    case kind::EQUAL:
      if (node[0].getType().isBoolean())
      {
        convertAndAssertIff(node, negated);
        break;
      }
      CVC4_FALLTHROUGH;
    default:
    {
      Node nnode = node;
      if (negated)
      {
        nnode = node.negate();
      }
      // Atoms
      assertClause(nnode, toCNF(node, negated));
  }
    break;
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
