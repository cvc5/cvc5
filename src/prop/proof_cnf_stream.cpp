/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
                               SatProofManager* satPM)
    : EnvObj(env),
      d_cnfStream(cnfStream),
      d_inputClauses(userContext()),
      d_lemmaClauses(userContext()),
      d_satPM(satPM),
      // Since the ProofCnfStream performs no equality reasoning, there is no
      // need to automatically add symmetry steps. Note that it is *safer* to
      // forbid this, since adding symmetry steps when proof nodes are being
      // updated may inadvertently generate cyclic proofs.
      //
      // This can happen for example if the proof cnf stream has a generator for
      // (= a b), whose proof depends on symmetry applied to (= b a). It does
      // not have a generator for (= b a). However if asked for a proof of the
      // fact (= b a) (after having expanded the proof of (= a b)), since it has
      // no genarotor for (= b a), a proof (= b a) can be generated via symmetry
      // on the proof of (= a b). As a result the assumption (= b a) would be
      // assigned a proof with assumption (= b a). This breakes the invariant of
      // the proof node manager of no cyclic proofs if the ASSUMPTION proof node
      // of both the assumption (= b a) we are asking the proof for and the
      // assumption (= b a) in the proof of (= a b) are the same.
      d_proof(
          env, nullptr, userContext(), "ProofCnfStream::LazyCDProof", false),
      d_blocked(userContext()),
      d_optClausesManager(userContext(), &d_proof, d_optClausesPfs)
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

std::vector<Node> ProofCnfStream::getInputClauses()
{
  std::vector<Node> cls;
  for (const Node& c : d_inputClauses)
  {
    cls.push_back(c);
  }
  return cls;
}

std::vector<Node> ProofCnfStream::getLemmaClauses()
{
  std::vector<Node> cls;
  for (const Node& c : d_lemmaClauses)
  {
    cls.push_back(c);
  }

  return cls;
}

std::vector<std::shared_ptr<ProofNode>> ProofCnfStream::getInputClausesProofs()
{
  std::vector<std::shared_ptr<ProofNode>> pfs;
  for (const Node& a : d_inputClauses)
  {
    pfs.push_back(d_proof.getProofFor(a));
  }
  return pfs;
}

std::vector<std::shared_ptr<ProofNode>> ProofCnfStream::getLemmaClausesProofs()
{
  std::vector<std::shared_ptr<ProofNode>> pfs;
  for (const Node& a : d_lemmaClauses)
  {
    pfs.push_back(d_proof.getProofFor(a));
  }
  return pfs;
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

Node ProofCnfStream::normalizeAndRegister(TNode clauseNode)
{
  Node normClauseNode = d_psb.factorReorderElimDoubleNeg(clauseNode);
  if (TraceIsOn("cnf") && normClauseNode != clauseNode)
  {
    Trace("cnf") << push
                 << "ProofCnfStream::normalizeAndRegister: steps to normalized "
                 << normClauseNode << "\n"
                 << pop;
  }
  if (d_input)
  {
    d_inputClauses.insert(normClauseNode);
  }
  else
  {
    d_lemmaClauses.insert(normClauseNode);
  }
  if (d_satPM)
  {
    d_satPM->registerSatAssumptions({normClauseNode});
  }
  return normClauseNode;
}

void ProofCnfStream::convertAndAssert(TNode node,
                                      bool negated,
                                      bool removable,
                                      bool input,
                                      ProofGenerator* pg)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", removable = " << (removable ? "true" : "false")
               << "), level " << userContext()->getLevel() << "\n";
  d_cnfStream.d_removable = removable;
  d_input = input;
  if (pg)
  {
    Trace("cnf") << "ProofCnfStream::convertAndAssert: pg: " << pg->identify()
                 << "\n";
    Node toJustify = negated ? node.notNode() : static_cast<Node>(node);
    d_proof.addLazyStep(toJustify,
                        pg,
                        PfRule::ASSUME,
                        true,
                        "ProofCnfStream::convertAndAssert:cnf");
  }
  convertAndAssert(node, negated);
  // process saved steps in buffer
  const std::vector<std::pair<Node, ProofStep>>& steps = d_psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    d_proof.addStep(step.first, step.second);
  }
  d_psb.clear();
  d_input = false;
}

void ProofCnfStream::convertAndAssert(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
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
        d_proof.addStep(node[0], PfRule::NOT_NOT_ELIM, {node.notNode()}, {});
        Trace("cnf")
            << "ProofCnfStream::convertAndAssert: NOT_NOT_ELIM added norm "
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
        d_proof.addStep(nnode, PfRule::NOT_NOT_ELIM, {node.notNode()}, {});
        Trace("cnf")
            << "ProofCnfStream::convertAndAssert: NOT_NOT_ELIM added norm "
            << nnode << "\n";
      }
      if (added && d_satPM)
      {
        // note that we do not need to do the normalization here since this is
        // not a clause and double negation is tracked in a dedicated manner
        // above
        d_satPM->registerSatAssumptions({nnode});
        if (d_input)
        {
          d_inputClauses.insert(nnode);
        }
        else
        {
          d_lemmaClauses.insert(nnode);
        }
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
  Assert(node.getKind() == kind::AND);
  if (!negated)
  {
    // If the node is a conjunction, we handle each conjunct separately
    NodeManager* nm = NodeManager::currentNM();
    for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
    {
      // Create a proof step for each n_i
      Node iNode = nm->mkConstInt(i);
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
  Trace("cnf") << pop;
}

void ProofCnfStream::convertAndAssertOr(TNode node, bool negated)
{
  Trace("cnf") << "ProofCnfStream::convertAndAssertOr(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n"
               << push;
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
      Node iNode = nm->mkConstInt(i);
      d_proof.addStep(
          node[i].notNode(), PfRule::NOT_OR_ELIM, {node.notNode()}, {iNode});
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
  Trace("cnf") << pop;
}

void ProofCnfStream::convertPropagation(TrustNode trn)
{
  Node proven = trn.getProven();
  Trace("cnf") << "ProofCnfStream::convertPropagation: proven explanation"
               << proven << "\n";
  // If we are not producing proofs in the theory engine there is no need to
  // keep track in d_proof of the clausification. We still need however to let
  // the SAT proof manager know that this clause is an assumption.
  bool proofLogging = trn.getGenerator() != nullptr;
  if (proofLogging)
  {
    Assert(trn.getGenerator()->getProofFor(proven)->isClosed());
    Trace("cnf-steps") << proven << " by explainPropagation "
                       << trn.identifyGenerator() << std::endl;
    d_proof.addLazyStep(proven,
                        trn.getGenerator(),
                        PfRule::ASSUME,
                        true,
                        "ProofCnfStream::convertPropagation");
  }
  // since the propagation is added directly to the SAT solver via theoryProxy,
  // do the transformation of the lemma E1 ^ ... ^ En => P into CNF here
  NodeManager* nm = NodeManager::currentNM();
  Node clauseImpliesElim;
  if (proofLogging)
  {
    clauseImpliesElim = nm->mkNode(kind::OR, proven[0].notNode(), proven[1]);
    Trace("cnf") << "ProofCnfStream::convertPropagation: adding "
                 << PfRule::IMPLIES_ELIM << " rule to conclude "
                 << clauseImpliesElim << "\n";
    d_proof.addStep(clauseImpliesElim, PfRule::IMPLIES_ELIM, {proven}, {});
  }
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
    clauseExp = nm->mkNode(kind::OR, disjunctsRes);
    if (proofLogging)
    {
      // add proof steps to convert into clause
      Node clauseAndNeg = nm->mkNode(kind::OR, disjunctsAndNeg);
      d_proof.addStep(clauseAndNeg, PfRule::CNF_AND_NEG, {}, {proven[0]});
      d_proof.addStep(clauseExp,
                      PfRule::RESOLUTION,
                      {clauseAndNeg, clauseImpliesElim},
                      {nm->mkConst(true), proven[0]});
    }
  }
  else
  {
    clauseExp = nm->mkNode(kind::OR, proven[0].notNode(), proven[1]);
  }
  d_currPropagationProcessed = normalizeAndRegister(clauseExp);
  // consume steps if clausification being recorded. If we are not logging it,
  // we need to add the clause as a closed step to the proof so that the SAT
  // proof does not have non-input formulas as assumptions. That clause is the
  // result of normalizeAndRegister, stored in d_currPropagationProcessed
  if (proofLogging)
  {
    const std::vector<std::pair<Node, ProofStep>>& steps = d_psb.getSteps();
    for (const std::pair<Node, ProofStep>& step : steps)
    {
      d_proof.addStep(step.first, step.second);
    }
    d_psb.clear();
  }
  else
  {
    d_proof.addStep(d_currPropagationProcessed,
                    PfRule::THEORY_LEMMA,
                    {},
                    {d_currPropagationProcessed});
  }
}

void ProofCnfStream::notifyCurrPropagationInsertedAtLevel(uint32_t explLevel)
{
  Assert(explLevel < (userContext()->getLevel() - 1));
  Assert(!d_currPropagationProcessed.isNull());
  Trace("cnf") << "Need to save curr propagation " << d_currPropagationProcessed
               << "'s proof in level " << explLevel + 1
               << " despite being currently in level "
               << userContext()->getLevel() << "\n";
  // Save into map the proof of the processed propagation. Note that
  // propagations must be explained eagerly, since their justification depends
  // on the theory engine and may be different if we only get its proof when the
  // SAT solver pops the user context. Not doing this may lead to open proofs.
  //
  // It's also necessary to copy the proof node, so we prevent unintended
  // updates to the saved proof. Not doing this may also lead to open proofs.
  std::shared_ptr<ProofNode> currPropagationProcPf =
      d_proof.getProofFor(d_currPropagationProcessed)->clone();
  Assert(currPropagationProcPf->getRule() != PfRule::ASSUME);
  Trace("cnf-debug") << "\t..saved pf {" << currPropagationProcPf << "} "
                     << *currPropagationProcPf.get() << "\n";
  d_optClausesPfs[explLevel + 1].push_back(currPropagationProcPf);
  // Notify SAT proof manager that the propagation (which is a SAT assumption)
  // had its level optimized
  if (d_satPM)
  {
    d_satPM->notifyAssumptionInsertedAtLevel(explLevel,
                                             d_currPropagationProcessed);
  }
  // Reset
  d_currPropagationProcessed = Node::null();
}

void ProofCnfStream::notifyClauseInsertedAtLevel(const SatClause& clause,
                                                 uint32_t clLevel)
{
  Trace("cnf") << "Need to save clause " << clause << " in level "
               << clLevel + 1 << " despite being currently in level "
               << userContext()->getLevel() << "\n";
  Node clauseNode = getClauseNode(clause);
  Trace("cnf") << "Node equivalent: " << clauseNode << "\n";
  Assert(clLevel < (userContext()->getLevel() - 1));
  // As above, also justify eagerly.
  std::shared_ptr<ProofNode> clauseCnfPf =
      d_proof.getProofFor(clauseNode)->clone();
  Assert(clauseCnfPf->getRule() != PfRule::ASSUME);
  d_optClausesPfs[clLevel + 1].push_back(clauseCnfPf);
  // Notify SAT proof manager that the propagation (which is a SAT assumption)
  // had its level optimized
  if (d_satPM)
  {
    d_satPM->notifyAssumptionInsertedAtLevel(clLevel, clauseNode);
  }
}

Node ProofCnfStream::getClauseNode(const SatClause& clause)
{
  std::vector<Node> clauseNodes;
  for (size_t i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = clause[i];
    clauseNodes.push_back(d_cnfStream.getNode(satLit));
  }
  // order children by node id
  std::sort(clauseNodes.begin(), clauseNodes.end());
  return NodeManager::currentNM()->mkNode(kind::OR, clauseNodes);
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
  n = n.getKind() == kind::NOT ? n[0] : n;
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
  Assert(node.getKind() == kind::AND) << "Expecting an AND expression!";
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
      Node iNode = nm->mkConstInt(i);
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
      Node iNode = nm->mkConstInt(i);
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
  Assert(!d_cnfStream.d_removable)
      << "Removable clauses can not contain Boolean structure";
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
}  // namespace cvc5::internal
