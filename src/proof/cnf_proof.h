/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A manager for CnfProofs.
 **
 ** A manager for CnfProofs.
 **
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__CNF_PROOF_H
#define CVC4__CNF_PROOF_H

#include <iosfwd>
#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "proof/clause_id.h"
#include "proof/sat_proof.h"
#include "util/maybe.h"

namespace CVC4 {
namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class CnfProof;

typedef std::unordered_map<prop::SatVariable, Expr> SatVarToExpr;
typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNode;
typedef std::unordered_set<ClauseId> ClauseIdSet;

typedef context::CDHashMap<ClauseId, Node> ClauseIdToNode;
typedef std::pair<Node, Node> NodePair;
typedef std::set<NodePair> NodePairSet;

typedef std::unordered_set<Node, NodeHashFunction> NodeSet;

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;

  /** Map from ClauseId to the assertion that lead to adding this clause **/
  ClauseIdToNode d_clauseToAssertion;

  /** Top of stack is assertion currently being converted to CNF **/
  std::vector<Node> d_currentAssertionStack;

  /** Top of stack is top-level fact currently being converted to CNF **/
  std::vector<Node> d_currentDefinitionStack;

  /** Map from ClauseId to the top-level fact that lead to adding this clause **/
  ClauseIdToNode d_clauseToDefinition;

  /** Top-level facts that follow from assertions during convertAndAssert **/
  NodeSet d_definitions;

  /** Map from top-level fact to facts/assertion that it follows from **/
  NodeToNode d_cnfDeps;

  ClauseIdSet d_explanations;

  // The clause ID of the unit clause defining the true SAT literal.
  ClauseId d_trueUnitClause;
  // The clause ID of the unit clause defining the false SAT literal.
  ClauseId d_falseUnitClause;

  Node getDefinitionForClause(ClauseId clause);

  std::string d_name;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream,
           context::Context* ctx,
           const std::string& name);
  ~CnfProof();

  Node getAtom(prop::SatVariable var);
  prop::SatLiteral getLiteral(TNode node);
  bool hasLiteral(TNode node);
  void ensureLiteral(TNode node, bool noPreregistration = false);

  void collectAtoms(const prop::SatClause* clause,
                    std::set<Node>& atoms);
  void collectAtomsForClauses(const IdToSatClause& clauses,
                              std::set<Node>& atoms);
  void collectAssertionsForClauses(const IdToSatClause& clauses,
                                   NodeSet& assertions);

  /** Methods for logging what the CnfStream does **/
  // map the clause back to the current assertion where it came from
  // if it is an explanation, it does not have a CNF proof since it is
  // already in CNF
  void registerConvertedClause(ClauseId clause, bool explanation=false);

  // The CNF proof has a special relationship to true and false.
  // In particular, it need to know the identity of clauses defining
  // canonical true and false literals in the underlying SAT solver.
  void registerTrueUnitClause(ClauseId clauseId);
  void registerFalseUnitClause(ClauseId clauseId);
  inline ClauseId getTrueUnitClause() { return d_trueUnitClause; };
  inline ClauseId getFalseUnitClause() { return d_falseUnitClause; };

  /** Clause is one of the clauses defining the node expression*/
  void setClauseDefinition(ClauseId clause, Node node);

  /** Clause is one of the clauses defining top-level assertion node*/
  void setClauseAssertion(ClauseId clause, Node node);

  void setCnfDependence(Node from, Node to);

  void pushCurrentAssertion(Node assertion); // the current assertion being converted
  void popCurrentAssertion();
  Node getCurrentAssertion();

  void pushCurrentDefinition(Node assertion); // the current Tseitin definition being converted
  void popCurrentDefinition();
  Node getCurrentDefinition();

  /**
   * Checks whether the assertion stack is empty.
   */
  bool isAssertionStackEmpty() const { return d_currentAssertionStack.empty(); }

  // accessors for the leaf assertions that are being converted to CNF
  bool isAssertion(Node node);
  Node getAssertionForClause(ClauseId clause);
};/* class CnfProof */

} /* CVC4 namespace */

#endif /* CVC4__CNF_PROOF_H */
