#include "tseitin_cnf_stream.h"

using namespace std;

using namespace CVC4;
using namespace mcsat;

TseitinCnfStream::TseitinCnfStream(context::Context* cnfContext)
: d_cnfContext(new context::Context())
, d_alreadyTranslated(d_cnfContext)
{

}

TseitinCnfStream::~TseitinCnfStream() {
  delete d_cnfContext;
}

Literal TseitinCnfStream::handleXor(TNode xorNode) {
  Assert(!alreadyTranslated(xorNode), "Atom already mapped!");
  Assert(xorNode.getKind() == kind::XOR, "Expecting an XOR expression!");
  Assert(xorNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  Literal a = toCnfRecursive(xorNode[0]);
  Literal b = toCnfRecursive(xorNode[1]);

  Literal xorLit = getLiteral(xorNode);

  outputClause(a, b, ~xorLit);
  outputClause(~a, ~b, ~xorLit);
  outputClause(a, ~b, xorLit);
  outputClause(~a, b, xorLit);

  return xorLit;
}

Literal TseitinCnfStream::handleOr(TNode orNode) {
  Assert(!alreadyTranslated(orNode), "Atom already mapped!");
  Assert(orNode.getKind() == kind::OR, "Expecting an OR expression!");
  Assert(orNode.getNumChildren() > 1, "Expecting more then 1 child!");

  // Number of children
  unsigned n_children = orNode.getNumChildren();

  // Transform all the children first
  TNode::const_iterator node_it = orNode.begin();
  TNode::const_iterator node_it_end = orNode.end();
  LiteralVector clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = toCnfRecursive(*node_it);
  }

  // Get the literal for this node
  Literal orLit = getLiteral(orNode);

  // lit <- (a_1 | a_2 | a_3 | ... | a_n)
  // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
  // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
  for(unsigned i = 0; i < n_children; ++i) {
    outputClause(orLit, ~clause[i]);
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[n_children] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  outputClause(clause);

  // Return the literal
  return orLit;
}

Literal TseitinCnfStream::handleAnd(TNode andNode) {
  Assert(!alreadyTranslated(andNode), "Atom already mapped!");
  Assert(andNode.getKind() == kind::AND, "Expecting an AND expression!");
  Assert(andNode.getNumChildren() > 1, "Expecting more than 1 child!");

  // Number of children
  unsigned n_children = andNode.getNumChildren();

  // Transform all the children first (remembering the negation)
  TNode::const_iterator node_it = andNode.begin();
  TNode::const_iterator node_it_end = andNode.end();
  LiteralVector clause(n_children + 1);
  for(int i = 0; node_it != node_it_end; ++node_it, ++i) {
    clause[i] = ~toCnfRecursive(*node_it);
  }

  // Get the literal for this node
  Literal andLit = getLiteral(andNode);

  // lit -> (a_1 & a_2 & a_3 & ... & a_n)
  // ~lit | (a_1 & a_2 & a_3 & ... & a_n)
  // (~lit | a_1) & (~lit | a_2) & ... & (~lit | a_n)
  for(unsigned i = 0; i < n_children; ++i) {
    outputClause(~andLit, ~clause[i]);
  }

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[n_children] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  outputClause(clause);

  return andLit;
}

Literal TseitinCnfStream::handleImplies(TNode impliesNode) {
  Assert(!alreadyTranslated(impliesNode), "Atom already mapped!");
  Assert(impliesNode.getKind() == kind::IMPLIES, "Expecting an IMPLIES expression!");
  Assert(impliesNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  // Convert the children to cnf
  Literal a = toCnfRecursive(impliesNode[0]);
  Literal b = toCnfRecursive(impliesNode[1]);

  Literal impliesLit = getLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  outputClause(~impliesLit, ~a, b);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  outputClause(a, impliesLit);
  outputClause(~b, impliesLit);

  return impliesLit;
}


Literal TseitinCnfStream::handleIff(TNode iffNode) {
  Assert(!alreadyTranslated(iffNode), "Atom already mapped!");
  Assert(iffNode.getKind() == kind::EQUAL, "Expecting an IFF expression!");
  Assert(iffNode.getNumChildren() == 2, "Expecting exactly 2 children!");

  Debug("mcsat::cnf") << "handleIff(" << iffNode << ")" << endl;

  // Convert the children to CNF
  Literal a = toCnfRecursive(iffNode[0]);
  Literal b = toCnfRecursive(iffNode[1]);

  // Get the now literal
  Literal iffLit = getLiteral(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  outputClause(~a, b, ~iffLit);
  outputClause(a, ~b, ~iffLit);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  outputClause(~a, ~b, iffLit);
  outputClause(a, b, iffLit);

  return iffLit;
}


Literal TseitinCnfStream::handleNot(TNode notNode) {
  Assert(!alreadyTranslated(notNode), "Atom already mapped!");
  Assert(notNode.getKind() == kind::NOT, "Expecting a NOT expression!");
  Assert(notNode.getNumChildren() == 1, "Expecting exactly 1 child!");

  Literal notLit = ~toCnfRecursive(notNode[0]);

  return notLit;
}

Literal TseitinCnfStream::handleIte(TNode iteNode) {
  Assert(!alreadyTranslated(iteNode), "Atom already mapped");
  Assert(iteNode.getKind() == kind::ITE);
  Assert(iteNode.getNumChildren() == 3);

  Debug("mcsat::cnf") << "handleIte(" << iteNode[0] << " " << iteNode[1] << " " << iteNode[2] << ")" << endl;

  Literal condLit = toCnfRecursive(iteNode[0]);
  Literal thenLit = toCnfRecursive(iteNode[1]);
  Literal elseLit = toCnfRecursive(iteNode[2]);

  Literal iteLit = getLiteral(iteNode);

  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  outputClause(~iteLit, thenLit, elseLit);
  outputClause(~iteLit, ~condLit, thenLit);
  outputClause(~iteLit, condLit, elseLit);

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  outputClause(iteLit, ~thenLit, ~elseLit);
  outputClause(iteLit, ~condLit, ~thenLit);
  outputClause(iteLit, condLit, ~elseLit);

  return iteLit;
}


Literal TseitinCnfStream::toCnfRecursive(TNode node, bool negated) {
  Debug("mcsat::cnf") << "toCNF(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  Literal nodeLit;
  Node negatedNode = node.notNode();

  // If the non-negated node has already been translated, get the translation
  if(alreadyTranslated(node)) {
    Debug("mcsat::cnf") << "toCNF(): already translated" << endl;
    nodeLit = getLiteral(node);
  } else {
    // Handle each Boolean operator case
    switch(node.getKind()) {
    case kind::NOT:
      nodeLit = handleNot(node);
      break;
    case kind::XOR:
      nodeLit = handleXor(node);
      break;
    case kind::ITE:
      nodeLit = handleIte(node);
      break;
    case kind::IMPLIES:
      nodeLit = handleImplies(node);
      break;
    case kind::OR:
      nodeLit = handleOr(node);
      break;
    case kind::AND:
      nodeLit = handleAnd(node);
      break;
    case kind::EQUAL:
      if(node[0].getType().isBoolean()) {
        // normally this is an IFF, but EQUAL is possible with pseudobooleans
        nodeLit = handleIff(node[0].eqNode(node[1]));
      } else {
        nodeLit = convertAtom(node);
      }
      break;
    default:
      {
        //TODO make sure this does not contain any boolean substructure
        nodeLit = convertAtom(node);
      }
      break;
    }
  }

  // Return the appropriate (negated) literal
  if (!negated) return nodeLit;
  else return ~nodeLit;
}

void TseitinCnfStream::topLevelAnd(TNode node, bool negated) {
  Assert(node.getKind() == kind::AND);
  if (!negated) {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      convert(*conjunct, false);
    }
  } else {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    LiteralVector clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCnfRecursive(*disjunct, true);
    }
    Assert(disjunct == node.end());
    outputClause(clause);
  }
}

void TseitinCnfStream::topLevelOr(TNode node, bool negated) {
  Assert(node.getKind() == kind::OR);
  if (!negated) {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    LiteralVector clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    for(int i = 0; i < nChildren; ++ disjunct, ++ i) {
      Assert( disjunct != node.end() );
      clause[i] = toCnfRecursive(*disjunct, false);
    }
    Assert(disjunct == node.end());
    outputClause(clause);
  } else {
    // If the node is a conjunction, we handle each conjunct separately
    for(TNode::const_iterator conjunct = node.begin(), node_end = node.end();
        conjunct != node_end; ++conjunct ) {
      convert(*conjunct, true);
    }
  }
}

void TseitinCnfStream::topLevelXor(TNode node, bool negated) {
  if (!negated) {
    // p XOR q
    Literal p = toCnfRecursive(node[0], false);
    Literal q = toCnfRecursive(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    LiteralVector clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    outputClause(clause1);
    LiteralVector clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    outputClause(clause2);
  } else {
    // !(p XOR q) is the same as p <=> q
    Literal p = toCnfRecursive(node[0], false);
    Literal q = toCnfRecursive(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    LiteralVector clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    outputClause(clause1);
    LiteralVector clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    outputClause(clause2);
  }
}

void TseitinCnfStream::topLevelIff(TNode node, bool negated) {
  if (!negated) {
    // p <=> q
    Literal p = toCnfRecursive(node[0], false);
    Literal q = toCnfRecursive(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    LiteralVector clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    outputClause(clause1);
    LiteralVector clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    outputClause(clause2);
  } else {
    // !(p <=> q) is the same as p XOR q
    Literal p = toCnfRecursive(node[0], false);
    Literal q = toCnfRecursive(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    LiteralVector clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    outputClause(clause1);
    LiteralVector clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    outputClause(clause2);
  }
}

void TseitinCnfStream::topLevelImplies(TNode node, bool negated) {
  if (!negated) {
    // p => q
    Literal p = toCnfRecursive(node[0], false);
    Literal q = toCnfRecursive(node[1], false);
    // Construct the clause ~p || q
    LiteralVector clause(2);
    clause[0] = ~p;
    clause[1] = q;
    outputClause(clause);
  } else {// Construct the
    // !(p => q) is the same as (p && ~q)
    convert(node[0], false);
    convert(node[1], true);
  }
}

void TseitinCnfStream::topLevelIte(TNode node, bool negated) {
  // ITE(p, q, r)
  Literal p = toCnfRecursive(node[0], false);
  Literal q = toCnfRecursive(node[1], negated);
  Literal r = toCnfRecursive(node[2], negated);
  // Construct the clauses:
  // (p => q) and (!p => r)
  LiteralVector clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  outputClause(clause1);
  LiteralVector clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  outputClause(clause2);
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void TseitinCnfStream::convert(TNode node, bool negated) {
  Debug("mcsat::cnf") << "topLevel(" << node << ", negated = " << (negated ? "true" : "false") << ")" << endl;

  switch(node.getKind()) {
  case kind::AND:
    topLevelAnd(node, negated);
    break;
  case kind::OR:
    topLevelOr(node, negated);
    break;
  case kind::XOR:
    topLevelXor(node, negated);
    break;
  case kind::IMPLIES:
    topLevelImplies(node, negated);
    break;
  case kind::ITE:
    topLevelIte(node, negated);
    break;
  case kind::NOT:
    convert(node[0], !negated);
    break;
  default:
    // Atoms
    outputClause(toCnfRecursive(node, negated));
    break;
  }
}
