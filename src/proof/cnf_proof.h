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
#include "proof/lemma_proof.h"
#include "proof/sat_proof.h"
#include "util/maybe.h"
#include "util/proof.h"

namespace CVC4 {
namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class CnfProof;

typedef std::unordered_map<prop::SatVariable, Expr> SatVarToExpr;
typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNode;
typedef std::unordered_set<ClauseId> ClauseIdSet;

typedef context::CDHashMap<ClauseId, Node> ClauseIdToNode;
typedef context::CDHashMap<Node, ProofRule, NodeHashFunction> NodeToProofRule;
typedef std::map<std::set<Node>, LemmaProofRecipe> LemmaToRecipe;
typedef std::pair<Node, Node> NodePair;
typedef std::set<NodePair> NodePairSet;

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;

  /** Map from ClauseId to the assertion that lead to adding this clause **/
  ClauseIdToNode d_clauseToAssertion;

  /** Map from assertion to reason for adding assertion  **/
  NodeToProofRule d_assertionToProofRule;

  /** Map from lemma to the recipe for proving it **/
  LemmaToRecipe d_lemmaToProofRecipe;

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

  bool isDefinition(Node node);

  Node getDefinitionForClause(ClauseId clause);

  std::string d_name;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream,
           context::Context* ctx,
           const std::string& name);


  Node getAtom(prop::SatVariable var);
  prop::SatLiteral getLiteral(TNode node);
  bool hasLiteral(TNode node);
  void ensureLiteral(TNode node, bool noPreregistration = false);

  void collectAtoms(const prop::SatClause* clause,
                    std::set<Node>& atoms);
  void collectAtomsForClauses(const IdToSatClause& clauses,
                              std::set<Node>& atoms);
  void collectAtomsAndRewritesForLemmas(const IdToSatClause& lemmaClauses,
                                        std::set<Node>& atoms,
                                        NodePairSet& rewrites);
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

  void registerAssertion(Node assertion, ProofRule reason);
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

  void setProofRecipe(LemmaProofRecipe* proofRecipe);
  LemmaProofRecipe getProofRecipe(const std::set<Node> &lemma);
  bool haveProofRecipe(const std::set<Node> &lemma);

  // accessors for the leaf assertions that are being converted to CNF
  bool isAssertion(Node node);
  ProofRule getProofRule(Node assertion);
  ProofRule getProofRule(ClauseId clause);
  Node getAssertionForClause(ClauseId clause);

  /** Virtual methods for printing things **/
  virtual void printAtomMapping(const std::set<Node>& atoms,
                                std::ostream& os,
                                std::ostream& paren) = 0;
  virtual void printAtomMapping(const std::set<Node>& atoms,
                           std::ostream& os,
                           std::ostream& paren,
                           ProofLetMap &letMap) = 0;

  // Detects whether a clause has x v ~x for some x
  // If so, returns the positive occurence's idx first, then the negative's
  static Maybe<std::pair<size_t, size_t>> detectTrivialTautology(
      const prop::SatClause& clause);
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

  void printAtomMapping(const std::set<Node>& atoms,
                        std::ostream& os,
                        std::ostream& paren) override;

  void printAtomMapping(const std::set<Node>& atoms,
                        std::ostream& os,
                        std::ostream& paren,
                        ProofLetMap& letMap) override;

  void printClause(const prop::SatClause& clause,
                   std::ostream& os,
                   std::ostream& paren) override;
  void printCnfProofForClause(ClauseId id,
                              const prop::SatClause* clause,
                              std::ostream& os,
                              std::ostream& paren) override;
};/* class LFSCCnfProof */

} /* CVC4 namespace */

#endif /* CVC4__CNF_PROOF_H */
