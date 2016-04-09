/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

#ifndef __CVC4__CNF_PROOF_H
#define __CVC4__CNF_PROOF_H

#include <ext/hash_map>
#include <ext/hash_set>
#include <iosfwd>

#include "context/cdhashmap.h"
#include "proof/clause_id.h"
#include "proof/sat_proof.h"
#include "util/proof.h"

namespace CVC4 {
namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class CnfProof;

typedef __gnu_cxx::hash_map<prop::SatVariable, Expr> SatVarToExpr;
typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeToNode;
typedef __gnu_cxx::hash_set<ClauseId> ClauseIdSet;

typedef context::CDHashMap<ClauseId, Node> ClauseIdToNode;
typedef context::CDHashMap<Node, ProofRule, NodeHashFunction> NodeToProofRule;
typedef context::CDHashMap<ClauseId, theory::TheoryId> ClauseIdToTheory;

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;

  /** Map from ClauseId to the assertion that lead to adding this clause **/
  ClauseIdToNode d_clauseToAssertion;

  /** Map from assertion to reason for adding assertion  **/
  NodeToProofRule d_assertionToProofRule;

  /** Map from assertion to the theory that added this assertion  **/
  ClauseIdToTheory d_clauseIdToOwnerTheory;

  /** The last theory to explain a lemma **/
  theory::TheoryId d_explainerTheory;

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

  bool isDefinition(Node node);

  Node getDefinitionForClause(ClauseId clause);

  std::string d_name;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream,
           context::Context* ctx,
           const std::string& name);


  Node getAtom(prop::SatVariable var);
  prop::SatLiteral getLiteral(TNode node);
  void collectAtoms(const prop::SatClause* clause,
                    NodeSet& atoms);
  void collectAtomsForClauses(const IdToSatClause& clauses,
                               NodeSet& atoms);
  void collectAssertionsForClauses(const IdToSatClause& clauses,
                                   NodeSet& assertions);

  /** Methods for logging what the CnfStream does **/
  // map the clause back to the current assertion where it came from
  // if it is an explanation, it does not have a CNF proof since it is
  // already in CNF
  void registerConvertedClause(ClauseId clause, bool explanation=false);

  /** Clause is one of the clauses defining the node expression*/
  void setClauseDefinition(ClauseId clause, Node node);

  /** Clause is one of the clauses defining top-level assertion node*/
  void setClauseAssertion(ClauseId clause, Node node);

  void registerAssertion(Node assertion, ProofRule reason);
  void setCnfDependence(Node from, Node to);

  void pushCurrentAssertion(Node assertion); // the current assertion being converted
  void popCurrentAssertion();
  Node getCurrentAssertion();

  void pushCurrentDefinition(Node assertion); // the current Tseitin definition being converted
  void popCurrentDefinition();
  Node getCurrentDefinition();

  void setExplainerTheory(theory::TheoryId theory);
  theory::TheoryId getExplainerTheory();
  theory::TheoryId getOwnerTheory(ClauseId clause);

  void registerExplanationLemma(ClauseId clauseId);

  // accessors for the leaf assertions that are being converted to CNF
  bool isAssertion(Node node);
  ProofRule getProofRule(Node assertion);
  ProofRule getProofRule(ClauseId clause);
  Node getAssertionForClause(ClauseId clause);

  /** Virtual methods for printing things **/
  virtual void printAtomMapping(const NodeSet& atoms,
                                std::ostream& os,
                                std::ostream& paren) = 0;

  virtual void printClause(const prop::SatClause& clause,
                           std::ostream& os,
                           std::ostream& paren) = 0;
  virtual void printCnfProofForClause(ClauseId id,
                                      const prop::SatClause* clause,
                                      std::ostream& os,
                                      std::ostream& paren) = 0;
  virtual ~CnfProof();
};/* class CnfProof */

class LFSCCnfProof : public CnfProof {
  Node clauseToNode( const prop::SatClause& clause,
                     std::map<Node, unsigned>& childIndex,
                     std::map<Node, bool>& childPol );
  bool printProofTopLevel(Node e, std::ostream& out);
public:
  LFSCCnfProof(CVC4::prop::CnfStream* cnfStream,
               context::Context* ctx,
               const std::string& name)
    : CnfProof(cnfStream, ctx, name)
  {}
  ~LFSCCnfProof() {}

  void printAtomMapping(const NodeSet& atoms,
                        std::ostream& os,
                        std::ostream& paren);

  void printClause(const prop::SatClause& clause,
                   std::ostream& os,
                   std::ostream& paren);
  void printCnfProofForClause(ClauseId id,
                              const prop::SatClause* clause,
                              std::ostream& os,
                              std::ostream& paren);
};/* class LFSCCnfProof */

} /* CVC4 namespace */

#endif /* __CVC4__CNF_PROOF_H */
