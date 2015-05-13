/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters, Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for CnfProofs.
 **
 ** A manager for CnfProofs.
 **
 **
 **/

#ifndef __CVC4__CNF_PROOF_H
#define __CVC4__CNF_PROOF_H

#include "cvc4_private.h"
#include "util/proof.h"
#include "proof/sat_proof.h"
#include "context/cdhashmap.h"

#include <ext/hash_set>
#include <ext/hash_map>
#include <iostream>

namespace CVC4 {
namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class CnfProof;

// typedef __gnu_cxx::hash_map < ClauseId, const prop::SatClause* > IdToClause;
// typedef __gnu_cxx::hash_map<Expr, prop::SatVariable, ExprHashFunction > ExprToSatVar;
typedef __gnu_cxx::hash_map<prop::SatVariable, Expr> SatVarToExpr;
typedef __gnu_cxx::hash_map<Node, Node, NodeHashFunction> NodeToNode;
typedef context::CDHashMap<ClauseId, Node> ClauseIdToNode;
typedef context::CDHashMap<Node, ProofRule, NodeHashFunction> NodeToProofRule;

class CnfProof {
protected:
  CVC4::prop::CnfStream* d_cnfStream;
  // ExprToSatVar d_atomToSatVar;
  // SatVarToExpr d_satVarToAtom;
  // IdToClause d_inputClauses;   

  /** Map from ClauseId to the assertion that lead to adding this clause **/
  ClauseIdToNode d_clauseToAssertion;

  /** Map from assertion to reason for adding assertion  **/
  NodeToProofRule d_assertionToProofRule;

  /** Top of stack is assertion currently being converted to CNF **/
  std::vector<Node> d_currentAssertionStack;

  /** Map from ClauseId to the top-level fact that lead to adding this clause **/
  ClauseIdToNode d_clauseToFact;

  /** Top-level facts that follow from assertions during convertAndAssert **/
  NodeSet d_topLevelFacts;
  
  /** Map from top-level fact to facts/assertion that it follows from **/
  NodeToNode d_cnfDeps;


  bool isTopLevelFact(Node node);

  Node getTopLevelFactForClause(ClauseId clause);
  
  std::string d_name;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream,
           context::Context* ctx,
           const std::string& name);
  
  // typedef IdToClause::const_iterator clause_iterator;
  // clause_iterator begin_input_clauses() const { return d_inputClauses.begin(); }
  // clause_iterator end_input_clauses() const { return d_inputClauses.end(); }
  //void addInputClause(ClauseId id, const prop::SatClause* clause); 
  

  Node getAtom(prop::SatVariable var);
  prop::SatLiteral getLiteral(TNode node);
  // Node getAssertion(ClauseId id);
  void collectAtoms(const prop::SatClause* clause,
                    NodeSet& atoms);
  void collectAtomsForClauses(const IdToClause& clauses,
                               NodeSet& atoms);
  void collectAssertionsForClauses(const IdToClause& clauses,
                                   NodeSet& assertions);

  /** Methods for logging what the CnfStream does **/
  // map the clause back to the current assertion where it came from
  // if it is an explanation, it does not have a CNF proof since it is
  // already in CNF
  void registerConvertedClause(ClauseId clause, bool explanation=false);
  void setClauseFact(ClauseId clause, Node fact);
  
  void registerAssertion(Node assertion, ProofRule reason);
  void setCnfDependence(Node from, Node to);
  void pushCurrentAssertion(Node assertion); // the current assertion being converted
  void popCurrentAssertion();

  Node getCurrentAssertion();

  // accessors for the leaf assertions that are being converted to CNF
  bool isAssertion(Node node);
  ProofRule getProofRule(Node assertion);
  ProofRule getProofRule(ClauseId clause);
  Node getAssertionForClause(ClauseId clause);

  
  /** Virtual methods for printing things **/
  virtual void printAtomMapping(const NodeSet& atoms,
                                std::ostream& os,
                                std::ostream& paren) = 0;
  // virtual void printClauses(std::ostream& os, std::ostream& paren) = 0;
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
  // void printPreprocess(std::ostream& os, std::ostream& paren);
  // void printInputClauses(std::ostream& os, std::ostream& paren);
  // void printTheoryLemmas(std::ostream& os, std::ostream& paren);

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
