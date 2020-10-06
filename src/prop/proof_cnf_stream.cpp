/*********************                                                        */
/*! \file proof_cnf_stream.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof-producing CNF stream
 **/

#include "prop/proof_cnf_stream.h"

#include "options/smt_options.h"
#include "prop/minisat/minisat.h"
#include "theory/builtin/proof_checker.h"

namespace CVC4 {
namespace prop {

ProofCnfStream::ProofCnfStream(context::UserContext* u,
                               CnfStream& cnfStream,
                               SatProofManager* satPM,
                               ProofNodeManager* pnm)
    : d_cnfStream(cnfStream),
      d_satPM(satPM),
      d_proof(pnm, nullptr, u, "ProofCnfStream::LazyCDProof"),
      d_blocked(u)
{
}

void ProofCnfStream::addBlocked(std::shared_ptr<ProofNode> pfn)
{
  d_blocked.insert(pfn);
}

bool ProofCnfStream::isBlocked(std::shared_ptr<ProofNode> pfn)
{
  return d_blocked.contains(pfn);
}

std::shared_ptr<ProofNode> ProofCnfStream::getProofFor(Node f)
{
  return d_proof.getProofFor(f);
}

bool ProofCnfStream::hasProofFor(Node f)
{
  return d_proof.hasStep(f) || d_proof.hasGenerator(f);
}

std::string ProofCnfStream::identify() const { return "ProofCnfStream"; }

void ProofCnfStream::normalizeAndRegister(TNode clauseNode)
{
  Node normClauseNode = d_psb.factorReorderElimDoubleNeg(clauseNode);
  if (Trace.isOn("cnf") && normClauseNode != clauseNode)
  {
    Trace("cnf") << push
                 << "ProofCnfStream::normalizeAndRegister: steps to normalized "
                 << normClauseNode << "\n"
                 << pop;
  }
  d_satPM->registerSatAssumptions({normClauseNode});
}

void ProofCnfStream::convertAndAssert(TNode node,
                                      bool negated,
                                      bool removable,
                                      ProofGenerator* pg)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", removable = " << (removable ? "true" : "false") << ")\n";
  d_removable = removable;
  if (pg)
  {
    Trace("cnf") << "ProofCnfStream::convertAndAssert: pg: " << pg->identify()
                 << "\n";
    Node toJustify = negated ? node.notNode() : static_cast<Node>(node);
    d_proof.addLazyStep(
        toJustify, pg, true, "ProofCnfStream::convertAndAssert:cnf");
  }
  convertAndAssert(node, negated);
  // process saved steps in buffer
  const std::vector<std::pair<Node, ProofStep>>& steps = d_psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    d_proof.addStep(step.first, step.second);
  }
  d_psb.clear();
}

void ProofCnfStream::convertAndAssert(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  switch (node.getKind())
  {
    case kind::AND: convertAndAssertAnd(node, negated); break;
    case kind::OR: convertAndAssertOr(node, negated); break;
    case kind::XOR: convertAndAssertXor(node, negated); break;
    case kind::IMPLIES: convertAndAssertImplies(node, negated); break;
    case kind::ITE: convertAndAssertIte(node, negated); break;
    case kind::NOT:
    {
      // track double negation elimination
      if (negated)
      {
        d_proof.addStep(node[0],
                        PfRule::MACRO_SR_PRED_TRANSFORM,
                        {node.notNode()},
                        {node[0]});
        Trace("cnf") << "ProofCnfStream::convertAndAssert: "
                        "MACRO_SR_PRED_TRANSFORM added norm "
                     << node[0] << "\n";
      }
      convertAndAssert(node[0], !negated);
      break;
    }
    case kind::EQUAL:
      if (node[0].getType().isBoolean())
      {
        convertAndAssertIff(node, negated);
        break;
      }
      CVC4_FALLTHROUGH;
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
        //   -------------- MACRO_SR_PRED_TRANSFORM
        //        n
        d_proof.addStep(
            nnode, PfRule::MACRO_SR_PRED_TRANSFORM, {node.notNode()}, {nnode});
        Trace("cnf") << "ProofCnfStream::convertAndAssert: "
                        "MACRO_SR_PRED_TRANSFORM added norm "
                     << nnode << "\n";
      }
      if (added)
      {
        // note that we do not need to do the normalization here since this is
        // not a clause and double negation is tracked in a dedicated manner
        // above
        d_satPM->registerSatAssumptions({nnode});
      }
    }
  }
}

void ProofCnfStream::convertAndAssertAnd(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertAnd(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  Assert(node.getKind() == kind::AND);
  if (!negated)
  {
    // If the node is a conjunction, we handle each conjunct separately
    NodeManager* nm = NodeManager::currentNM();
    for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
    {
      // Create a proof step for each n_i
      Node iNode = nm->mkConst<Rational>(i);
      d_proof.addStep(node[i], PfRule::AND_ELIM, {node}, {iNode});
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
      Node clauseNode = NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
      d_proof.addStep(clauseNode, PfRule::NOT_AND, {node.notNode()}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertAnd: NOT_AND added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
  }
}

void ProofCnfStream::convertAndAssertOr(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertOr(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  Assert(node.getKind() == kind::OR);
  if (!negated)
  {
    // If the node is a disjunction, we construct a clause and assert it
    unsigned size = node.getNumChildren();
    SatClause clause(size);
    for (unsigned i = 0; i < size; ++i)
    {
      clause[i] = toCNF(node[i], false);
    }
    normalizeAndRegister(node);
    d_cnfStream.assertClause(node, clause);
  }
  else
  {
    // If the node is a negated disjunction, we handle it as a conjunction of
    // the negated arguments
    NodeManager* nm = NodeManager::currentNM();
    for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
    {
      // Create a proof step for each (not n_i)
      Node iNode = nm->mkConst<Rational>(i);
      d_proof.addStep(
          node[i].notNode(), PfRule::NOT_OR_ELIM, {node.notNode()}, {iNode});
      Trace("cnf") << "ProofCnfStream::convertAndAssertOr: NOT_OR_ELIM " << i
                   << " added norm  " << node[i].notNode() << "\n";
      convertAndAssert(node[i], true);
    }
  }
}

void ProofCnfStream::convertAndAssertXor(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertXor(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  if (!negated)
  {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    bool added;
    NodeManager* nm = NodeManager::currentNM();
    // Construct the clause (~p v ~q)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    added = d_cnfStream.assertClause(node, clause1);
    if (added)
    {
      Node clauseNode =
          nm->mkNode(kind::OR, node[0].notNode(), node[1].notNode());
      d_proof.addStep(clauseNode, PfRule::XOR_ELIM2, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertXor: XOR_ELIM2 added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
    // Construct the clause (p v q)
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    added = d_cnfStream.assertClause(node, clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0], node[1]);
      d_proof.addStep(clauseNode, PfRule::XOR_ELIM1, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertXor: XOR_ELIM1 added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
  }
  else
  {
    // ~(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    bool added;
    NodeManager* nm = NodeManager::currentNM();
    // Construct the clause ~p v q
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    added = d_cnfStream.assertClause(node.negate(), clause1);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0].notNode(), node[1]);
      d_proof.addStep(clauseNode, PfRule::NOT_XOR_ELIM2, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertXor: NOT_XOR_ELIM2 added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
    // Construct the clause ~q v p
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    added = d_cnfStream.assertClause(node.negate(), clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0], node[1].notNode());
      d_proof.addStep(clauseNode, PfRule::NOT_XOR_ELIM1, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertXor: NOT_XOR_ELIM1 added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
  }
}

void ProofCnfStream::convertAndAssertIff(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertIff(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  if (!negated)
  {
    // p <=> q
    Trace("cnf") << push;
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    Trace("cnf") << pop;
    bool added;
    NodeManager* nm = NodeManager::currentNM();
    // Construct the clauses ~p v q
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    added = d_cnfStream.assertClause(node, clause1);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0].notNode(), node[1]);
      d_proof.addStep(clauseNode, PfRule::EQUIV_ELIM1, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIff: EQUIV_ELIM1 added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
    // Construct the clauses ~q v p
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    added = d_cnfStream.assertClause(node, clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0], node[1].notNode());
      d_proof.addStep(clauseNode, PfRule::EQUIV_ELIM2, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIff: EQUIV_ELIM2 added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
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
    NodeManager* nm = NodeManager::currentNM();
    // Construct the clauses ~p v ~q
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    added = d_cnfStream.assertClause(node.negate(), clause1);
    if (added)
    {
      Node clauseNode =
          nm->mkNode(kind::OR, node[0].notNode(), node[1].notNode());
      d_proof.addStep(
          clauseNode, PfRule::NOT_EQUIV_ELIM2, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIff: NOT_EQUIV_ELIM2 added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
    // Construct the clauses q v p
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    added = d_cnfStream.assertClause(node.negate(), clause2);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0], node[1]);
      d_proof.addStep(
          clauseNode, PfRule::NOT_EQUIV_ELIM1, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIff: NOT_EQUIV_ELIM1 added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
  }
}

void ProofCnfStream::convertAndAssertImplies(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertImplies(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
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
      Node clauseNode = NodeManager::currentNM()->mkNode(
          kind::OR, node[0].notNode(), node[1]);
      d_proof.addStep(clauseNode, PfRule::IMPLIES_ELIM, {node}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertImplies: IMPLIES_ELIM added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
  }
  else
  {
    // ~(p => q) is the same as p ^ ~q
    // process p
    convertAndAssert(node[0], false);
    d_proof.addStep(node[0], PfRule::NOT_IMPLIES_ELIM1, {node.notNode()}, {});
    Trace("cnf")
        << "ProofCnfStream::convertAndAssertImplies: NOT_IMPLIES_ELIM1 added "
        << node[0] << "\n";
    // process ~q
    convertAndAssert(node[1], true);
    d_proof.addStep(
        node[1].notNode(), PfRule::NOT_IMPLIES_ELIM2, {node.notNode()}, {});
    Trace("cnf")
        << "ProofCnfStream::convertAndAssertImplies: NOT_IMPLIES_ELIM2 added "
        << node[1].notNode() << "\n";
  }
}

void ProofCnfStream::convertAndAssertIte(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertIte(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);
  bool added;
  NodeManager* nm = NodeManager::currentNM();
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
      Node clauseNode = nm->mkNode(kind::OR, node[0].notNode(), node[1]);
      d_proof.addStep(clauseNode, PfRule::ITE_ELIM1, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIte: ITE_ELIM1 added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
    else
    {
      Node clauseNode =
          nm->mkNode(kind::OR, node[0].notNode(), node[1].notNode());
      d_proof.addStep(clauseNode, PfRule::NOT_ITE_ELIM1, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIte: NOT_ITE_ELIM1 added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
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
      Node clauseNode = nm->mkNode(kind::OR, node[0], node[2]);
      d_proof.addStep(clauseNode, PfRule::ITE_ELIM2, {node}, {});
      Trace("cnf") << "ProofCnfStream::convertAndAssertIte: ITE_ELIM2 added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
    else
    {
      Node clauseNode = nm->mkNode(kind::OR, node[0], node[2].notNode());
      d_proof.addStep(clauseNode, PfRule::NOT_ITE_ELIM2, {node.notNode()}, {});
      Trace("cnf")
          << "ProofCnfStream::convertAndAssertIte: NOT_ITE_ELIM2 added "
          << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
    }
  }
}

void ProofCnfStream::convertPropagation(theory::TrustNode trn)
{
  Node proven = trn.getProven();
  Trace("cnf") << "ProofCnfStream::convertPropagation: proven explanation"
               << proven << "\n";
  Assert(trn.getGenerator());
  Assert(trn.getGenerator()->getProofFor(proven)->isClosed());
  Trace("cnf-steps") << proven << " by explainPropagation "
                     << trn.identifyGenerator() << std::endl;
  d_proof.addLazyStep(
      proven, trn.getGenerator(), true, "ProofCnfStream::convertPropagation");
  // since the propagation is added directly to the SAT solver via theoryProxy,
  // do the transformation of the lemma E1 ^ ... ^ En => P into CNF here
  NodeManager* nm = NodeManager::currentNM();
  Node clauseImpliesElim = nm->mkNode(kind::OR, proven[0].notNode(), proven[1]);
  Trace("cnf") << "ProofCnfStream::convertPropagation: adding "
               << PfRule::IMPLIES_ELIM << " rule to conclude "
               << clauseImpliesElim << "\n";
  d_proof.addStep(clauseImpliesElim, PfRule::IMPLIES_ELIM, {proven}, {});
  Node clauseExp;
  // need to eliminate AND
  if (proven[0].getKind() == kind::AND)
  {
    std::vector<Node> disjunctsAndNeg{proven[0]};
    std::vector<Node> disjunctsRes;
    for (unsigned i = 0, size = proven[0].getNumChildren(); i < size; ++i)
    {
      disjunctsAndNeg.push_back(proven[0][i].notNode());
      disjunctsRes.push_back(proven[0][i].notNode());
    }
    disjunctsRes.push_back(proven[1]);
    Node clauseAndNeg = nm->mkNode(kind::OR, disjunctsAndNeg);
    // add proof steps to convert into clause
    d_proof.addStep(clauseAndNeg, PfRule::CNF_AND_NEG, {}, {proven[0]});
    clauseExp = nm->mkNode(kind::OR, disjunctsRes);
    d_proof.addStep(clauseExp,
                    PfRule::RESOLUTION,
                    {clauseAndNeg, clauseImpliesElim},
                    {proven[0]});
  }
  else
  {
    clauseExp = clauseImpliesElim;
  }
  normalizeAndRegister(clauseExp);
  // consume steps
  const std::vector<std::pair<Node, ProofStep>>& steps = d_psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    d_proof.addStep(step.first, step.second);
  }
  d_psb.clear();
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
    case kind::AND: lit = handleAnd(node); break;
    case kind::OR: lit = handleOr(node); break;
    case kind::XOR: lit = handleXor(node); break;
    case kind::IMPLIES: lit = handleImplies(node); break;
    case kind::ITE: lit = handleIte(node); break;
    case kind::NOT: lit = ~toCNF(node[0]); break;
    case kind::EQUAL:
      lit = node[0].getType().isBoolean() ? handleIff(node)
                                          : d_cnfStream.convertAtom(node);
      break;
    default: { lit = d_cnfStream.convertAtom(node);
    }
    break;
  }
  // Return the (maybe negated) literal
  return !negated ? lit : ~lit;
}

SatLiteral ProofCnfStream::handleAnd(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == kind::AND) << "Expecting an AND expression!";
  Assert(node.getNumChildren() > 1) << "Expecting more than 1 child!";
  Assert(!d_removable) << "Removable clauses cannot contain Boolean structure";
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
  NodeManager* nm = NodeManager::currentNM();
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
      Node clauseNode = nm->mkNode(kind::OR, node.notNode(), node[i]);
      Node iNode = nm->mkConst<Rational>(i);
      d_proof.addStep(clauseNode, PfRule::CNF_AND_POS, {}, {node, iNode});
      Trace("cnf") << "ProofCnfStream::handleAnd: CNF_AND_POS " << i
                   << " added " << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
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
    Node clauseNode = nm->mkNode(kind::OR, disjuncts);
    d_proof.addStep(clauseNode, PfRule::CNF_AND_NEG, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleAnd: CNF_AND_NEG added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleOr(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == kind::OR) << "Expecting an OR expression!";
  Assert(node.getNumChildren() > 1) << "Expecting more then 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
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
  NodeManager* nm = NodeManager::currentNM();
  // lit <- (a_1 | a_2 | a_3 | ... | a_n)
  // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
  // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
  for (unsigned i = 0; i < size; ++i)
  {
    added = d_cnfStream.assertClause(node, lit, ~clause[i]);
    if (added)
    {
      Node clauseNode = nm->mkNode(kind::OR, node, node[i].notNode());
      Node iNode = nm->mkConst<Rational>(i);
      d_proof.addStep(clauseNode, PfRule::CNF_OR_NEG, {}, {node, iNode});
      Trace("cnf") << "ProofCnfStream::handleOr: CNF_OR_NEG " << i << " added "
                   << clauseNode << "\n";
      normalizeAndRegister(clauseNode);
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
    Node clauseNode = nm->mkNode(kind::OR, disjuncts);
    d_proof.addStep(clauseNode, PfRule::CNF_OR_POS, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleOr: CNF_OR_POS added " << clauseNode
                 << "\n";
    normalizeAndRegister(clauseNode);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleXor(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == kind::XOR) << "Expecting an XOR expression!";
  Assert(node.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "ProofCnfStream::handleXor(" << node << ")\n";
  SatLiteral a = toCNF(node[0]);
  SatLiteral b = toCNF(node[1]);
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  added = d_cnfStream.assertClause(node.negate(), a, b, ~lit);
  if (added)
  {
    Node clauseNode = NodeManager::currentNM()->mkNode(
        kind::OR, node.notNode(), node[0], node[1]);
    d_proof.addStep(clauseNode, PfRule::CNF_XOR_POS1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_POS1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node.negate(), ~a, ~b, ~lit);
  if (added)
  {
    Node clauseNode = NodeManager::currentNM()->mkNode(
        kind::OR, node.notNode(), node[0].notNode(), node[1].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_XOR_POS2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_POS2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node, a, ~b, lit);
  if (added)
  {
    Node clauseNode = NodeManager::currentNM()->mkNode(
        kind::OR, node, node[0], node[1].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_XOR_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_NEG2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node, ~a, b, lit);
  if (added)
  {
    Node clauseNode = NodeManager::currentNM()->mkNode(
        kind::OR, node, node[0].notNode(), node[1]);
    d_proof.addStep(clauseNode, PfRule::CNF_XOR_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleXor: CNF_XOR_NEG1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleIff(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == kind::EQUAL) << "Expecting an EQUAL expression!";
  Assert(node.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Trace("cnf") << "handleIff(" << node << ")\n";
  // Convert the children to CNF
  SatLiteral a = toCNF(node[0]);
  SatLiteral b = toCNF(node[1]);
  // Create literal for the node
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = NodeManager::currentNM();
  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  added = d_cnfStream.assertClause(node.negate(), ~a, b, ~lit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(kind::OR, node.notNode(), node[0].notNode(), node[1]);
    d_proof.addStep(clauseNode, PfRule::CNF_EQUIV_POS1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_POS1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node.negate(), a, ~b, ~lit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(kind::OR, node.notNode(), node[0], node[1].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_EQUIV_POS2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_POS2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
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
        nm->mkNode(kind::OR, node, node[0].notNode(), node[1].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_EQUIV_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_NEG2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node, a, b, lit);
  if (added)
  {
    Node clauseNode = nm->mkNode(kind::OR, node, node[0], node[1]);
    d_proof.addStep(clauseNode, PfRule::CNF_EQUIV_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIff: CNF_EQUIV_NEG1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleImplies(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == kind::IMPLIES) << "Expecting an IMPLIES expression!";
  Assert(node.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "ProofCnfStream::handleImplies(" << node << ")\n";
  // Convert the children to cnf
  SatLiteral a = toCNF(node[0]);
  SatLiteral b = toCNF(node[1]);
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = NodeManager::currentNM();
  // lit -> (a->b)
  // ~lit | ~ a | b
  added = d_cnfStream.assertClause(node.negate(), ~lit, ~a, b);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(kind::OR, node.notNode(), node[0].notNode(), node[1]);
    d_proof.addStep(clauseNode, PfRule::CNF_IMPLIES_POS, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleImplies: CNF_IMPLIES_POS added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  added = d_cnfStream.assertClause(node, a, lit);
  if (added)
  {
    Node clauseNode = nm->mkNode(kind::OR, node, node[0]);
    d_proof.addStep(clauseNode, PfRule::CNF_IMPLIES_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleImplies: CNF_IMPLIES_NEG1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node, ~b, lit);
  if (added)
  {
    Node clauseNode = nm->mkNode(kind::OR, node, node[1].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_IMPLIES_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleImplies: CNF_IMPLIES_NEG2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  return lit;
}

SatLiteral ProofCnfStream::handleIte(TNode node)
{
  Assert(!d_cnfStream.hasLiteral(node)) << "Atom already mapped!";
  Assert(node.getKind() == kind::ITE);
  Assert(node.getNumChildren() == 3);
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleIte(" << node[0] << " " << node[1] << " " << node[2]
               << ")\n";
  SatLiteral condLit = toCNF(node[0]);
  SatLiteral thenLit = toCNF(node[1]);
  SatLiteral elseLit = toCNF(node[2]);
  // create literal to the node
  SatLiteral lit = d_cnfStream.newLiteral(node);
  bool added;
  NodeManager* nm = NodeManager::currentNM();
  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  added = d_cnfStream.assertClause(node.negate(), ~lit, thenLit, elseLit);
  if (added)
  {
    Node clauseNode = nm->mkNode(kind::OR, node.notNode(), node[1], node[2]);
    d_proof.addStep(clauseNode, PfRule::CNF_ITE_POS3, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_POS3 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node.negate(), ~lit, ~condLit, thenLit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(kind::OR, node.notNode(), node[0].notNode(), node[1]);
    d_proof.addStep(clauseNode, PfRule::CNF_ITE_POS1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_POS1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node.negate(), ~lit, condLit, elseLit);
  if (added)
  {
    Node clauseNode = nm->mkNode(kind::OR, node.notNode(), node[0], node[2]);
    d_proof.addStep(clauseNode, PfRule::CNF_ITE_POS2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_POS2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
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
        nm->mkNode(kind::OR, node, node[1].notNode(), node[2].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_ITE_NEG3, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_NEG3 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node, lit, ~condLit, ~thenLit);
  if (added)
  {
    Node clauseNode =
        nm->mkNode(kind::OR, node, node[0].notNode(), node[1].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_ITE_NEG1, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_NEG1 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  added = d_cnfStream.assertClause(node, lit, condLit, ~elseLit);
  if (added)
  {
    Node clauseNode = nm->mkNode(kind::OR, node, node[0], node[2].notNode());
    d_proof.addStep(clauseNode, PfRule::CNF_ITE_NEG2, {}, {node});
    Trace("cnf") << "ProofCnfStream::handleIte: CNF_ITE_NEG2 added "
                 << clauseNode << "\n";
    normalizeAndRegister(clauseNode);
  }
  return lit;
}

}  // namespace prop
}  // namespace CVC4
