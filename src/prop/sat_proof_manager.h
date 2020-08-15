/*********************                                                        */
/*! \file sat_proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager for Minisat
 **/

#include "cvc4_private.h"

#ifndef CVC4__SAT_PROOF_MANAGER_H
#define CVC4__SAT_PROOF_MANAGER_H

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/proof.h"
#include "expr/proof_node_manager.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/sat_solver_types.h"

namespace Minisat {
class Solver;
}

namespace CVC4 {

namespace prop {

/**
 * This class is responsible for managing the proof output of SmtEngine, as
 * well as setting up the global proof checker and proof node manager.
 */
class SatProofManager
{
 public:
  SatProofManager(Minisat::Solver* solver,
                  TheoryProxy* proxy,
                  context::UserContext* userContext,
                  ProofNodeManager* pnm);

  void startResChain(Minisat::Clause& start);
  // resolution with unit clause ~lit, to be justified
  void addResolutionStep(Minisat::Lit lit);
  // resolution with clause using lit as pivot. Sign determines whether it's
  // being removed positively from the given clause or the implicit one it's
  // being resolved against
  void addResolutionStep(Minisat::Clause& clause,
                         Minisat::Lit lit);
  void endResChain(Minisat::Lit lit);
  void endResChain(Minisat::Clause& clause);
  void endResChain(Node conclusion);

  /** If lit is not already justified, try to. Otherwise no-op. */
  void tryJustifyingLit(prop::SatLiteral lit);

  void finalizeProof(Node inConflictNode,
                     const std::vector<SatLiteral>& inConflict);
  void finalizeProof(Minisat::Clause& inConflict);
  void finalizeProof(Minisat::Lit inConflict);
  void finalizeProof();
  void storeUnitConflict(Minisat::Lit inConflict);

  CDProof* getProof() { return &d_proof; }

 private:
  /** The sat solver to which we are managing proofs */
  Minisat::Solver* d_solver;
  /** A pointer to theory proxy */
  TheoryProxy* d_proxy;

  /** The proof node manager */
  ProofNodeManager* d_pnm;

  /** The resolution proof */
  CDProof d_proof;

  /** The false node */
  Node d_false;

  /** resolution steps accumulator for chain resolution */
  std::vector<std::pair<Node, Node>> d_resolution;

  /** A placeholder that may be used to store the literal with the final conflict */
  SatLiteral d_conflictLit;

  Node getClauseNode(SatLiteral satLit);
  Node getClauseNode(const Minisat::Clause& clause);
  void printClause(const Minisat::Clause& clause);



}; /* class SatProofManager */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__SAT_PROOF_MANAGER_H */
