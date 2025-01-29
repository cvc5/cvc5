/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the proof-producing CNF stream.
 */

#include "prop/proof_cnf_stream.h"

#include "options/smt_options.h"
#include "prop/minisat/minisat.h"
#include "theory/builtin/proof_checker.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace prop {

ProofCnfStream::ProofCnfStream(Env& env,
                               CnfStream& cnfStream,
                               PropPfManager* ppm)
    : EnvObj(env),
      d_cnfStream(cnfStream),
      d_ppm(ppm),
      d_proof(ppm->getCnfProof())
{
}

void ProofCnfStream::convertAndAssert(TNode node,
                                      bool negated,
                                      bool removable,
                                      bool input,
                                      ProofGenerator* pg)
{
  // this method is re-entrant due to lemmas sent during preregistration of new
  // lemmas, thus we must remember and revert d_input below.
  bool backupInput = d_input;
  Trace("cnf") << "ProofCnfStream::convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", removable = " << (removable ? "true" : "false")
               << ", input = " << (input ? "true" : "false") << "), level "
               << userContext()->getLevel() << "\n";
  d_cnfStream.d_removable = removable;
  d_input = input;
  if (pg)
  {
    Trace("cnf") << "ProofCnfStream::convertAndAssert: pg: " << pg->identify()
                 << "\n";
    Node toJustify = negated ? node.notNode() : static_cast<Node>(node);
    d_proof->addLazyStep(toJustify,
                         pg,
                         TrustId::NONE,
                         true,
                         "ProofCnfStream::convertAndAssert:cnf");
  }
  convertAndAssert(node, negated);
  d_input = backupInput;
}

void ProofCnfStream::convertAndAssert(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  switch (node.getKind())
  {
    case Kind::AND: convertAndAssertAnd(node, negated); break;
    case Kind::OR: convertAndAssertOr(node, negated); break;
    case Kind::XOR: convertAndAssertXor(node, negated); break;
    case Kind::IMPLIES: convertAndAssertImplies(node, negated); break;
    case Kind::ITE: convertAndAssertIte(node, negated); break;
    case Kind::NOT:
    {
      // track double negation elimination
      if (negated)
      {
        d_proof->addStep(
            node[0], ProofRule::NOT_NOT_ELIM, {node.notNode()}, {});
        Trace("cnf")
            << "ProofCnfStream::convertAndAssert: NOT_NOT_ELIM added norm "
            << node[0] << "\n";
      }
      convertAndAssert(node[0], !negated);
      break;
    }
    case Kind::EQUAL:
      if (node[0].getType().isBoolean())
      {
        convertAndAssertIff(node, negated);
        break;
      }
      CVC5_FALLTHROUGH;
    default:
    {
      // negate
      Node nnode = negated ? node.negate() : static_cast<Node>(node);
      // Atoms
      SatLiteral lit = toCNF(node, negated);
      bool added = d_cnfStream.assertClause(nnode, lit);
      if (negated && added && nnode != node.notNode())
      {
        // track double negation elimination
        //    (not (not n))
        //   -------------- NOT_NOT_ELIM
        //        n
        d_proof->addStep(nnode, ProofRule::NOT_NOT_ELIM, {node.notNode()}, {});
        Trace("cnf")
            << "ProofCnfStream::convertAndAssert: NOT_NOT_ELIM added norm "
            << nnode << "\n";
      }
      if (added)
      {
        // note that we do not need to do the normalization here since this is
        // not a clause and double negation is tracked in a dedicated manner
        // above
        d_ppm->normalizeAndRegister(nnode, d_input, false);
      }
    }
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertAnd(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertAnd(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  Assert(node.getKind() == Kind::AND);
  if (!negated)
  {
    // If the node is a conjunction, we handle each conjunct separately
    NodeManager* nm = nodeManager();
    for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
    {
      // Create a proof step for each n_i
      Node iNode = nm->mkConstInt(i);
      d_proof->addStep(node[i], ProofRule::AND_ELIM, {node}, {iNode});
      Trace("cnf") << "ProofCnfStream::convertAndAssertAnd: AND_ELIM " << i
                   << " added norm " << node[i] << "\n";
      convertAndAssert(node[i], false);
    }
  }
  else
  {
    // If the node is a disjunction, we construct a clause and assert it
    unsigned i, size = node.getNumChildren();
    SatClause clause(size);
    for (i = 0; i < size; ++i)
    {
      clause[i] = toCNF(node[i], true);
    }
    bool added = d_cnfStream.assertClause(node.negate(), clause);
    // register proof step
    if (added)
    {
      std::vector<Node> disjuncts;
      for (i = 0; i < size; ++i)
      {
        disjuncts.push_back(node[i].notNode());
      }
      Node clauseNode = nodeManager()->mkNode(Kind::OR, disjuncts);
      d_proof->addStep(clauseNode, ProofRule::NOT_AND, {node.notNode()}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertAnd: NOT_AND added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertOr(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertOr(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  Assert(node.getKind() == Kind::OR);
  if (!negated)
  {
    // If the node is a disjunction, we construct a clause and assert it
    unsigned size = node.getNumChildren();
    SatClause clause(size);
    for (unsigned i = 0; i < size; ++i)
    {
      clause[i] = toCNF(node[i], false);
    }
    d_ppm->normalizeAndRegister(node, d_input);
    d_cnfStream.assertClause(node, clause);
  }
  else
  {
    // If the node is a negated disjunction, we handle it as a conjunction of
    // the negated arguments
    NodeManager* nm = nodeManager();
    for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
    {
      // Create a proof step for each (not n_i)
      Node iNode = nm->mkConstInt(i);
      d_proof->addStep(
          node[i].notNode(), ProofRule::NOT_OR_ELIM, {node.notNode()}, {iNode});
      Trace("cnf") << "ProofCnfStream::convertAndAssertOr: NOT_OR_ELIM " << i
                   << " added norm  " << node[i].notNode() << "\n";
      convertAndAssert(node[i], true);
    }
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertXor(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertXor(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  if (!negated)
  {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    bool added;
    NodeManager* nm = nodeManager();
    // Construct the clause (~p v ~q)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    added = d_cnfStream.assertClause(node, clause1);
    if (added)
    {
      Node clauseNode =
          nm->mkNode(Kind::OR, node[0].notNode(), node[1].notNode());
      d_proof->addStep(clauseNode, ProofRule::XOR_ELIM2, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertXor: XOR_ELIM2 added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
    // Construct the clause (p v q)
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    added = d_cnfStream.assertClause(node, clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0], node[1]);
      d_proof->addStep(clauseNode, ProofRule::XOR_ELIM1, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertXor: XOR_ELIM1 added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  else
  {
    // ~(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    bool added;
    NodeManager* nm = nodeManager();
    // Construct the clause ~p v q
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    added = d_cnfStream.assertClause(node.negate(), clause1);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0].notNode(), node[1]);
      d_proof->addStep(
          clauseNode, ProofRule::NOT_XOR_ELIM2, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertXor: NOT_XOR_ELIM2 added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
    // Construct the clause ~q v p
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    added = d_cnfStream.assertClause(node.negate(), clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0], node[1].notNode());
      d_proof->addStep(
          clauseNode, ProofRule::NOT_XOR_ELIM1, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertXor: NOT_XOR_ELIM1 added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertIff(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertIff(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  if (!negated)
  {
    // p <=> q
    Trace("cnf") << push;
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    Trace("cnf") << pop;
    bool added;
    NodeManager* nm = nodeManager();
    // Construct the clauses ~p v q
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    added = d_cnfStream.assertClause(node, clause1);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0].notNode(), node[1]);
      d_proof->addStep(clauseNode, ProofRule::EQUIV_ELIM1, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIff: EQUIV_ELIM1 added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
    // Construct the clauses ~q v p
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    added = d_cnfStream.assertClause(node, clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0], node[1].notNode());
      d_proof->addStep(clauseNode, ProofRule::EQUIV_ELIM2, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIff: EQUIV_ELIM2 added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  else
  {
    // ~(p <=> q) is the same as p XOR q
    Trace("cnf") << push;
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    Trace("cnf") << pop;
    bool added;
    NodeManager* nm = nodeManager();
    // Construct the clauses ~p v ~q
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    added = d_cnfStream.assertClause(node.negate(), clause1);
    if (added)
    {
      Node clauseNode =
          nm->mkNode(Kind::OR, node[0].notNode(), node[1].notNode());
      d_proof->addStep(
          clauseNode, ProofRule::NOT_EQUIV_ELIM2, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIff: NOT_EQUIV_ELIM2 added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
    // Construct the clauses q v p
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    added = d_cnfStream.assertClause(node.negate(), clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0], node[1]);
      d_proof->addStep(
          clauseNode, ProofRule::NOT_EQUIV_ELIM1, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIff: NOT_EQUIV_ELIM1 added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertImplies(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertImplies(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  if (!negated)
  {
    // ~p v q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    bool added = d_cnfStream.assertClause(node, clause);
    if (added)
    {
      Node clauseNode =
          nodeManager()->mkNode(Kind::OR, node[0].notNode(), node[1]);
      d_proof->addStep(clauseNode, ProofRule::IMPLIES_ELIM, {node}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertImplies: IMPLIES_ELIM added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  else
  {
    // ~(p => q) is the same as p ^ ~q
    // process p
    convertAndAssert(node[0], false);
    d_proof->addStep(
        node[0], ProofRule::NOT_IMPLIES_ELIM1, {node.notNode()}, {});
    Trace("cnf")
        << "ProofCnfStream::convertAndAssertImplies: NOT_IMPLIES_ELIM1 added "
        << node[0] << "\n";
    // process ~q
    convertAndAssert(node[1], true);
    d_proof->addStep(
        node[1].notNode(), ProofRule::NOT_IMPLIES_ELIM2, {node.notNode()}, {});
    Trace("cnf")
        << "ProofCnfStream::convertAndAssertImplies: NOT_IMPLIES_ELIM2 added "
        << node[1].notNode() << "\n";
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertIte(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertIte(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  bool added;
  NodeManager* nm = nodeManager();
  // Construct the clauses:
  // (~p v q) and (p v r)
  //
  // Note that below q and r can be used directly because whether they are
  // negated has been push to the literal definitions above
  Node nnode = negated ? node.negate() : static_cast<Node>(node);
  // (~p v q)
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  added = d_cnfStream.assertClause(nnode, clause1);
  if (added)
  {
    // redo the negation here to avoid silent double negation elimination
    if (!negated)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0].notNode(), node[1]);
      d_proof->addStep(clauseNode, ProofRule::ITE_ELIM1, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIte: ITE_ELIM1 added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
    else
    {
      Node clauseNode =
          nm->mkNode(Kind::OR, node[0].notNode(), node[1].notNode());
      d_proof->addStep(
          clauseNode, ProofRule::NOT_ITE_ELIM1, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIte: NOT_ITE_ELIM1 added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  // (p v r)
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  added = d_cnfStream.assertClause(nnode, clause2);
  if (added)
  {
    // redo the negation here to avoid silent double negation elimination
    if (!negated)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0], node[2]);
      d_proof->addStep(clauseNode, ProofRule::ITE_ELIM2, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIte: ITE_ELIM2 added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
    else
    {
      Node clauseNode = nm->mkNode(Kind::OR, node[0], node[2].notNode());
      d_proof->addStep(
          clauseNode, ProofRule::NOT_ITE_ELIM2, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIte: NOT_ITE_ELIM2 added "
          << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  Trace("cnf") << pop;
}

void ProofCnfStream::ensureLiteral(TNode n)
{
  Trace("cnf") << "ProofCnfStream::ensureLiteral(" << n << ")\n";
  if (d_cnfStream.hasLiteral(n))
  {
    d_cnfStream.ensureMappingForLiteral(n);
    return;
  }
  // remove top level negation. We don't need to track this because it's a
  // literal.
  n = n.getKind() == Kind::NOT ? n[0] : n;
  if (d_env.theoryOf(n) == theory::THEORY_BOOL && !n.isVar())
  {
    // These are not removable
    d_cnfStream.d_removable = false;
    SatLiteral lit = toCNF(n, false);
    // Store backward-mappings
    // These may already exist
    d_cnfStream.d_literalToNodeMap.insert_safe(lit, n);
    d_cnfStream.d_literalToNodeMap.insert_safe(~lit, n.notNode());
  }
  else
  {
    d_cnfStream.convertAtom(n);
  }
}

bool ProofCnfStream::hasLiteral(TNode n) const
{
  return d_cnfStream.hasLiteral(n);
}

SatLiteral ProofCnfStream::getLiteral(TNode node)
{
  return d_cnfStream.getLiteral(node);
}

void ProofCnfStream::getBooleanVariables(
    std::vector<TNode>& outputVariables) const
{
  d_cnfStream.getBooleanVariables(outputVariables);
}

SatLiteral ProofCnfStream::toCNF(TNode node, bool negated)
{
  Trace("cnf") << "toCNF(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  SatLiteral lit;
  // If the node has already has a literal, return it (maybe negated)
  if (d_cnfStream.hasLiteral(node))
  {
    Trace("cnf") << "toCNF(): already translated\n";
    lit = d_cnfStream.getLiteral(node);
    // Return the (maybe negated) literal
    return !negated ? lit : ~lit;
  }

  // Handle each Boolean operator case
  switch (node.getKind())
  {
    case Kind::AND: lit = handleAnd(node); break;
    case Kind::OR: lit = handleOr(node); break;
    case Kind::XOR: lit = handleXor(node); break;
    case Kind::IMPLIES: lit = handleImplies(node); break;
    case Kind::ITE: lit = handleIte(node); break;
    case Kind::NOT: lit = ~toCNF(node[0]); break;
    case Kind::EQUAL:
      lit = node[0].getType().isBoolean() ? handleIff(node)
                                          : d_cnfStream.convertAtom(node);
      break;
    default:
    {
      lit = d_cnfStream.convertAtom(node);
    }
    break;
  }
  // Return the (maybe negated) literal
  return !negated ? lit : ~lit;
}

SatLiteral ProofCnfStream::handleAnd(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == Kind::AND) << "Expecting an AND expression!";
  Assert(node.getNumChildren() > 1) << "Expecting more than 1 child!";
  Assert(!d_cnfStream.d_removable)
      << "Removable clauses cannot contain Boolean structure";
  Trace("cnf") << "ProofCnfStream::handleAnd(" << node << ")\n";
  // Number of children
  unsigned size = node.getNumChildren();
  // Transform all the children first (remembering the negation)
  SatClause clause(size + 1);
  for (unsigned i = 0; i < size; ++i)
  {
    Trace("cnf") << push;
    clause[i] = ~toCNF(node[i]);
    Trace("cnf") << pop;
  }
  // Create literal for the node
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = nodeManager();
  // lit -> (a_1 & a_2 & a_3 & ... & a_n)
  // ~lit | (a_1 & a_2 & a_3 & ... & a_n)
  // (~lit | a_1) & (~lit | a_2) & ... & (~lit | a_n)
  for (unsigned i = 0; i < size; ++i)
  {
    Trace("cnf") << push;
    added = d_cnfStream.assertClause(node.negate(), ~lit, ~clause[i]);
    Trace("cnf") << pop;
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node.notNode(), node[i]);
      Node iNode = nm->mkConstInt(i);
      d_proof->addStep(clauseNode, ProofRule::CNF_AND_POS, {}, {node, iNode});
      Trace("cnf") << "ProofCnfStream::handleAnd: CNF_AND_POS " << i
                   << " added " << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[size] = lit;
  // This needs to go last, as the clause might get modified by the SAT solver
  Trace("cnf") << push;
  added = d_cnfStream.assertClause(node, clause);
  Trace("cnf") << pop;
  if (added)
  {
    std::vector<Node> disjuncts{node};
    for (unsigned i = 0; i < size; ++i)
    {
      disjuncts.push_back(node[i].notNode());
    }
    Node clauseNode = nm->mkNode(Kind::OR, disjuncts);
    d_proof->addStep(clauseNode, ProofRule::CNF_AND_NEG, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleAnd: CNF_AND_NEG added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleOr(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == Kind::OR) << "Expecting an OR expression!";
  Assert(node.getNumChildren() > 1) << "Expecting more then 1 child!";
  Assert(!d_cnfStream.d_removable)
      << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "ProofCnfStream::handleOr(" << node << ")\n";
  // Number of children
  unsigned size = node.getNumChildren();
  // Transform all the children first
  SatClause clause(size + 1);
  for (unsigned i = 0; i < size; ++i)
  {
    clause[i] = toCNF(node[i]);
  }
  // Create literal for the node
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = nodeManager();
  // lit <- (a_1 | a_2 | a_3 | ... | a_n)
  // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
  // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
  for (unsigned i = 0; i < size; ++i)
  {
    added = d_cnfStream.assertClause(node, lit, ~clause[i]);
    if (added)
    {
      Node clauseNode = nm->mkNode(Kind::OR, node, node[i].notNode());
      Node iNode = nm->mkConstInt(i);
      d_proof->addStep(clauseNode, ProofRule::CNF_OR_NEG, {}, {node, iNode});
      Trace("cnf") << "ProofCnfStream::handleOr: CNF_OR_NEG " << i << " added "
                   << clauseNode << "\n";
      d_ppm->normalizeAndRegister(clauseNode, d_input);
    }
  }
  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[size] = ~lit;
  // This needs to go last, as the clause might get modified by the SAT solver
  added = d_cnfStream.assertClause(node.negate(), clause);
  if (added)
  {
    std::vector<Node> disjuncts{node.notNode()};
    for (unsigned i = 0; i < size; ++i)
    {
      disjuncts.push_back(node[i]);
    }
    Node clauseNode = nm->mkNode(Kind::OR, disjuncts);
    d_proof->addStep(clauseNode, ProofRule::CNF_OR_POS, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleOr: CNF_OR_POS added " << clauseNode
                 << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleXor(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == Kind::XOR) << "Expecting an XOR expression!";
  Assert(node.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_cnfStream.d_removable)
      << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "ProofCnfStream::handleXor(" << node << ")\n";
  SatLiteral a = toCNF(node[0]);
  SatLiteral b = toCNF(node[1]);
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  added = d_cnfStream.assertClause(node.negate(), a, b, ~lit);
  if (added)
  {
    Node clauseNode =
        nodeManager()->mkNode(Kind::OR, node.notNode(), node[0], node[1]);
    d_proof->addStep(clauseNode, ProofRule::CNF_XOR_POS1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_POS1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node.negate(), ~a, ~b, ~lit);
  if (added)
  {
    Node clauseNode = nodeManager()->mkNode(
        Kind::OR, node.notNode(), node[0].notNode(), node[1].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_XOR_POS2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_POS2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node, a, ~b, lit);
  if (added)
  {
    Node clauseNode =
        nodeManager()->mkNode(Kind::OR, node, node[0], node[1].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_XOR_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_NEG2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node, ~a, b, lit);
  if (added)
  {
    Node clauseNode =
        nodeManager()->mkNode(Kind::OR, node, node[0].notNode(), node[1]);
    d_proof->addStep(clauseNode, ProofRule::CNF_XOR_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_NEG1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleIff(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == Kind::EQUAL) << "Expecting an EQUAL expression!";
  Assert(node.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Trace("cnf") << "handleIff(" << node << ")\n";
  // Convert the children to CNF
  SatLiteral a = toCNF(node[0]);
  SatLiteral b = toCNF(node[1]);
  // Create literal for the node
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = nodeManager();
  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  added = d_cnfStream.assertClause(node.negate(), ~a, b, ~lit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node.notNode(), node[0].notNode(), node[1]);
    d_proof->addStep(clauseNode, ProofRule::CNF_EQUIV_POS1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_POS1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node.negate(), a, ~b, ~lit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node.notNode(), node[0], node[1].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_EQUIV_POS2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_POS2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  added = d_cnfStream.assertClause(node, ~a, ~b, lit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node, node[0].notNode(), node[1].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_EQUIV_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_NEG2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node, a, b, lit);
  if (added)
  {
    Node clauseNode = nm->mkNode(Kind::OR, node, node[0], node[1]);
    d_proof->addStep(clauseNode, ProofRule::CNF_EQUIV_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_NEG1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleImplies(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == Kind::IMPLIES) << "Expecting an IMPLIES expression!";
  Assert(node.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_cnfStream.d_removable)
      << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "ProofCnfStream::handleImplies(" << node << ")\n";
  // Convert the children to cnf
  SatLiteral a = toCNF(node[0]);
  SatLiteral b = toCNF(node[1]);
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = nodeManager();
  // lit -> (a->b)
  // ~lit | ~ a | b
  added = d_cnfStream.assertClause(node.negate(), ~lit, ~a, b);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node.notNode(), node[0].notNode(), node[1]);
    d_proof->addStep(clauseNode, ProofRule::CNF_IMPLIES_POS, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleImplies: CNF_IMPLIES_POS added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  added = d_cnfStream.assertClause(node, a, lit);
  if (added)
  {
    Node clauseNode = nm->mkNode(Kind::OR, node, node[0]);
    d_proof->addStep(clauseNode, ProofRule::CNF_IMPLIES_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleImplies: CNF_IMPLIES_NEG1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node, ~b, lit);
  if (added)
  {
    Node clauseNode = nm->mkNode(Kind::OR, node, node[1].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_IMPLIES_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleImplies: CNF_IMPLIES_NEG2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleIte(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == Kind::ITE);
  Assert(node.getNumChildren() == 3);
  Assert(!d_cnfStream.d_removable)
      << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleIte(" << node[0] << " " << node[1] << " " << node[2]
               << ")\n";
  SatLiteral condLit = toCNF(node[0]);
  SatLiteral thenLit = toCNF(node[1]);
  SatLiteral elseLit = toCNF(node[2]);
  // create literal to the node
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = nodeManager();
  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  added = d_cnfStream.assertClause(node.negate(), ~lit, thenLit, elseLit);
  if (added)
  {
    Node clauseNode = nm->mkNode(Kind::OR, node.notNode(), node[1], node[2]);
    d_proof->addStep(clauseNode, ProofRule::CNF_ITE_POS3, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_POS3 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node.negate(), ~lit, ~condLit, thenLit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node.notNode(), node[0].notNode(), node[1]);
    d_proof->addStep(clauseNode, ProofRule::CNF_ITE_POS1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_POS1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node.negate(), ~lit, condLit, elseLit);
  if (added)
  {
    Node clauseNode = nm->mkNode(Kind::OR, node.notNode(), node[0], node[2]);
    d_proof->addStep(clauseNode, ProofRule::CNF_ITE_POS2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_POS2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  added = d_cnfStream.assertClause(node, lit, ~thenLit, ~elseLit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node, node[1].notNode(), node[2].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_ITE_NEG3, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_NEG3 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node, lit, ~condLit, ~thenLit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(Kind::OR, node, node[0].notNode(), node[1].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_ITE_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_NEG1 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  added = d_cnfStream.assertClause(node, lit, condLit, ~elseLit);
  if (added)
  {
    Node clauseNode = nm->mkNode(Kind::OR, node, node[0], node[2].notNode());
    d_proof->addStep(clauseNode, ProofRule::CNF_ITE_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_NEG2 added "
                 << clauseNode << "\n";
    d_ppm->normalizeAndRegister(clauseNode, d_input);
  }
  return lit;
}

void ProofCnfStream::dumpDimacs(std::ostream& out,
                                const std::vector<Node>& clauses)
{
  d_cnfStream.dumpDimacs(out, clauses);
}

void ProofCnfStream::dumpDimacs(std::ostream& out,
                                const std::vector<Node>& clauses,
                                const std::vector<Node>& auxUnits)
{
  d_cnfStream.dumpDimacs(out, clauses, auxUnits);
}

}  // namespace prop
}  // namespace cvc5::internal
