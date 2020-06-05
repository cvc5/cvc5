/*********************                                                        */
/*! \file new_proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A new global manager for Proofs
 **/

#include "cvc4_private.h"

#ifndef CVC4__NEW_PROOF_MANAGER_H
#define CVC4__NEW_PROOF_MANAGER_H

#include <iosfwd>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "expr/proof.h"
#include "proof/proof.h"
#include "proof/proof_utils.h"
#include "prop/minisat/core/Solver.h"
#include "prop/sat_solver_types.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"
#include "theory/theory.h"
#include "util/statistics_registry.h"

namespace CVC4 {

// forward declarations
namespace Minisat {
class Solver;
}  // namespace Minisat

namespace prop {
class CnfStream;
}  // namespace prop

class SmtEngine;

namespace prop {
typedef uint64_t SatVariable;
class SatLiteral;
typedef std::vector<SatLiteral> SatClause;
}  // namespace prop

class Resolution
{
 public:
  // clause being resolved with another clause using the pivot with the given
  // sign
  ClauseId d_id;
  Node d_piv;
  unsigned d_sign;

  Resolution(ClauseId id, Node piv = Node::null(), unsigned sign = 0)
      : d_id(id), d_piv(piv), d_sign(sign)
  {
  }
};

class NewProofManager
{
 protected:
  LogicInfo d_logic;

 public:
  NewProofManager();
  ~NewProofManager();

  static NewProofManager* currentPM();

  /* ------------ BEGIN SAT solver handling ------------ */

  void setProofNodeManager();

  void setSatSolver(Minisat::Solver* solver);

  void addLitDef(prop::SatLiteral lit, Node litNode);

  void registerClause(Minisat::Solver::TLit lit);

  void registerClause(prop::SatLiteral satLit);

  void registerClause(Minisat::Solver::TClause& clause);

  void startResChain(Minisat::Solver::TClause& start);

  // resolution with unit clause ~lit, to be justified
  void addResolutionStep(Minisat::Solver::TLit lit);

  // resolution with clause using lit as pivot. Sign determines whether it's
  // being removed positively from the given clause or the implicit one it's
  // being resolved against
  void addResolutionStep(Minisat::Solver::TClause& clause,
                         Minisat::Solver::TLit lit);
  void endResChain(Minisat::Solver::TLit lit);
  void endResChain(Minisat::Solver::TClause& clause);
  void endResChain(ClauseId id);

  void finalizeProof(ClauseId conflict_id);
  void finalizeProof(Minisat::Solver::TLit lit);

  inline void printLit(const Minisat::Solver::TLit lit);
  inline void printClause(const Minisat::Solver::TClause& clause);

  /* ------------ END Defining maps between SAT / solver info ------------ */

  void addStep(Node expected,
               PfRule rule,
               const std::vector<Node>& children,
               const std::vector<Node>& args);

  void printInternalProof();

  /**
   * if given node is a clause, normalize it by ordering (according to node ids)
   * and removal of duplicates.
   */
  Node factorAndReorder(Node n);

  inline CDProof* getProof() const { return d_cdproof.get(); }

 private:
  /**************** BEGIN stuff for using proof nodes */

  /** The proof object. It does not care about context. */
  std::shared_ptr<CDProof> d_cdproof;

  /**************** END stuff for using proof nodes */

  /* pointer to core SAT solver. Probably this should go through SMT engine,
   * prop engine */
  Minisat::Solver* d_solver;

  /** maps clauses to the nodes they correspond to */
  std::map<Node, ClauseId> d_nodeToClauseId;
  std::map<ClauseId, Node> d_clauseIdToNode;

  /** maps SAT literals to the nodes they correspond to */
  std::map<prop::SatLiteral, Node> d_litToNode;
  std::map<Node, prop::SatLiteral> d_nodeToLit;

  std::map<prop::SatLiteral, ClauseId> d_litToClauseId;
  std::map<ClauseId, prop::SatLiteral> d_clauseIdToLit;

  std::vector<std::pair<Node, Node>> d_resolution;

  unsigned d_nextId;

  /** If lit is not already justified, try to. Otherwise no-op. */
  void tryJustifyingLit(prop::SatLiteral lit);
}; /* class ProofManager */

}  // namespace CVC4

#endif /* CVC4__NEW_PROOF_MANAGER_H */
