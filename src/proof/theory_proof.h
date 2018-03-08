/*********************                                                        */
/*! \file theory_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_PROOF_H
#define __CVC4__THEORY_PROOF_H

#include <iosfwd>
#include <unordered_map>
#include <unordered_set>

#include "expr/expr.h"
#include "proof/clause_id.h"
#include "prop/sat_solver_types.h"
#include "util/proof.h"
#include "proof/proof_utils.h"
#include "theory/uf/equality_engine.h"
namespace CVC4 {

namespace theory {
class Theory;
} /* namespace CVC4::theory */

typedef std::unordered_map < ClauseId, prop::SatClause* > IdToSatClause;

class TheoryProof;

typedef std::unordered_set<Expr, ExprHashFunction > ExprSet;
typedef std::map<theory::TheoryId, TheoryProof* > TheoryProofTable;

typedef std::set<theory::TheoryId> TheoryIdSet;
typedef std::map<Expr, TheoryIdSet> ExprToTheoryIds;

class TheoryProofEngine {
protected:
  ExprSet d_registrationCache;
  TheoryProofTable d_theoryProofTable;
  ExprToTheoryIds d_exprToTheoryIds;

  /**
   * Returns whether the theory is currently supported in proof
   * production mode.
   */
  bool supportedTheory(theory::TheoryId id);
public:

  TheoryProofEngine();
  virtual ~TheoryProofEngine();

  /**
   * Print the theory term (could be an atom) by delegating to the proper theory.
   *
   * @param term
   * @param os
   */
  virtual void printLetTerm(Expr term, std::ostream& os) = 0;
  virtual void printBoundTerm(Expr term, std::ostream& os,
                              const ProofLetMap& map) = 0;

  /**
   * Print the proof representation of the given sort.
   *
   * @param os
   */
  virtual void printSort(Type type, std::ostream& os) = 0;

  /**
   * Go over the assertions and register all terms with the theories.
   *
   * @param os
   * @param paren closing parenthesis
   */
  virtual void registerTermsFromAssertions() = 0;

  /**
   * Print the theory assertions (arbitrary formulas over
   * theory atoms)
   *
   * @param os
   * @param paren closing parenthesis
   */
  virtual void printAssertions(std::ostream& os, std::ostream& paren) = 0;
  /**
   * Print variable declarations that need to appear within the proof,
   * e.g. skolemized variables.
   *
   * @param os
   * @param paren closing parenthesis
   */
  virtual void printDeferredDeclarations(std::ostream& os, std::ostream& paren) = 0;

  /**
   * Print aliasing declarations.
   *
   * @param os
   * @param paren closing parenthesis
   */
  virtual void printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) = 0;

  /**
   * Print proofs of all the theory lemmas (must prove
   * actual clause used in resolution proof).
   *
   * @param os
   * @param paren
   */
  virtual void printTheoryLemmas(const IdToSatClause& lemmas, std::ostream& os,
                                 std::ostream& paren, ProofLetMap& map) = 0;

  /**
   * Register theory atom (ensures all terms and atoms are declared).
   *
   * @param atom
   */
  void registerTerm(Expr atom);

  /**
   * Ensures that a theory proof class for the given theory is created.
   * This method can be invoked regardless of whether the "proof" option
   * has been set.
   *
   * @param theory
   */
  void registerTheory(theory::Theory* theory);
  /**
   * Additional configuration of the theory proof class for the given theory.
   * This method should only be invoked when the "proof" option has been set.
   *
   * @param theory
   */
  void finishRegisterTheory(theory::Theory* theory);

  theory::TheoryId getTheoryForLemma(const prop::SatClause* clause);
  TheoryProof* getTheoryProof(theory::TheoryId id);

  void markTermForFutureRegistration(Expr term, theory::TheoryId id);

  void printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap);

  virtual void printTheoryTerm(Expr term, std::ostream& os, const ProofLetMap& map) = 0;

  bool printsAsBool(const Node &n);
};

class LFSCTheoryProofEngine : public TheoryProofEngine {
  void bind(Expr term, ProofLetMap& map, Bindings& let_order);
public:
  LFSCTheoryProofEngine()
    : TheoryProofEngine() {}

  void printTheoryTerm(Expr term,
                       std::ostream& os,
                       const ProofLetMap& map) override;

  void registerTermsFromAssertions() override;
  void printSortDeclarations(std::ostream& os, std::ostream& paren);
  void printTermDeclarations(std::ostream& os, std::ostream& paren);
  void printCoreTerm(Expr term, std::ostream& os, const ProofLetMap& map);
  void printLetTerm(Expr term, std::ostream& os) override;
  void printBoundTerm(Expr term,
                      std::ostream& os,
                      const ProofLetMap& map) override;
  void printAssertions(std::ostream& os, std::ostream& paren) override;
  void printLemmaRewrites(NodePairSet& rewrites,
                          std::ostream& os,
                          std::ostream& paren);
  void printDeferredDeclarations(std::ostream& os,
                                 std::ostream& paren) override;
  void printAliasingDeclarations(std::ostream& os,
                                 std::ostream& paren,
                                 const ProofLetMap& globalLetMap) override;
  void printTheoryLemmas(const IdToSatClause& lemmas,
                         std::ostream& os,
                         std::ostream& paren,
                         ProofLetMap& map) override;
  void printSort(Type type, std::ostream& os) override;

  void performExtraRegistrations();

  void finalizeBvConflicts(const IdToSatClause& lemmas, std::ostream& os);

private:
  static void dumpTheoryLemmas(const IdToSatClause& lemmas);

  // TODO: this function should be moved into the BV prover.

  std::map<Node, std::string> d_assertionToRewrite;
};

class TheoryProof {
protected:
  // Pointer to the theory for this proof
  theory::Theory* d_theory;
  TheoryProofEngine* d_proofEngine;
public:
  TheoryProof(theory::Theory* th, TheoryProofEngine* proofEngine)
    : d_theory(th)
    , d_proofEngine(proofEngine)
  {}
  virtual ~TheoryProof() {};
  /**
   * Print a term belonging some theory, not necessarily this one.
   *
   * @param term expresion representing term
   * @param os output stream
   */
  void printTerm(Expr term, std::ostream& os, const ProofLetMap& map) {
    d_proofEngine->printBoundTerm(term, os, map);
  }
  /**
   * Print a term belonging to THIS theory.
   *
   * @param term expression representing term
   * @param os output stream
   */
  virtual void printOwnedTerm(Expr term, std::ostream& os, const ProofLetMap& map) = 0;
  /**
   * Print the proof representation of the given type that belongs to some theory.
   *
   * @param type
   * @param os
   */
  void printSort(Type type, std::ostream& os) {
    d_proofEngine->printSort(type, os);
  }


   //Copied from uf_proof.cpp and array_proof.cpp
   inline static bool match(TNode n1, TNode n2, theory::TheoryId);

   //Copied from uf_proof.cpp and array_proof.cpp
   inline static Node eqNode(TNode n1, TNode n2) {
		return NodeManager::currentNM()->mkNode(kind::EQUAL, n1, n2);
   }

  /**
   * Helper function for ProofUF::toStreamRecLFSC and ProofArray::toStreamRecLFSC
   */


   void assertAndPrint(std::ostream& out,
						  const theory::eq::EqProof& pf,
						  const ProofLetMap& map,
						  const theory::TheoryId theoryId,
						  int* neg,
						  std::shared_ptr<theory::eq::EqProof> subTrans, 
						  theory::eq::EqProof::PrettyPrinter* pPrettyPrinter = nullptr);

  /**
   * Helper function for ProofUF::toStreamRecLFSC and ProofArray::toStreamRecLFSC
   */
	void transitivityPrinterHelper(theory::TheoryId theoryId,
                        bool evenLengthSequence,
                        bool sequenceOver,
                        int i,
                        const theory::eq::EqProof& pf,
                        const ProofLetMap& map,
                        const Node& n2,
                        const std::string ss1String,
                        std::stringstream* ss,
                        Node& n1,
                        Node& nodeAfterEqualitySequence);


  /**
   * Print the proof representation of the given type that belongs to THIS theory.
   *
   * @param type
   * @param os
   */
  virtual void printOwnedSort(Type type, std::ostream& os) = 0;
  /**
   * Print a proof for the theory lemmas. Must prove
   * clause representing lemmas to be used in resolution proof.
   *
   * @param os output stream
   */
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma,
                                     std::ostream& os,
                                     std::ostream& paren,
                                     const ProofLetMap& map);
  /**
   * Print the sorts declarations for this theory.
   *
   * @param os
   * @param paren
   */
  virtual void printSortDeclarations(std::ostream& os, std::ostream& paren) = 0;
  /**
   * Print the term declarations for this theory.
   *
   * @param os
   * @param paren
   */
  virtual void printTermDeclarations(std::ostream& os, std::ostream& paren) = 0;
  /**
   * Print any deferred variable/sorts declarations for this theory
   * (those that need to appear inside the actual proof).
   *
   * @param os
   * @param paren
   */
  virtual void printDeferredDeclarations(std::ostream& os, std::ostream& paren) = 0;
  /**
   * Print any aliasing declarations.
   *
   * @param os
   * @param paren
   */
  virtual void printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap) = 0;
  /**
   * Register a term of this theory that appears in the proof.
   *
   * @param term
   */
  virtual void registerTerm(Expr term) = 0;
  /**
   * Print a proof for the disequality of two constants that belong to this theory.
   *
   * @param term
   */
  virtual void printConstantDisequalityProof(std::ostream& os, Expr c1, Expr c2, const ProofLetMap &globalLetMap);
  /**
   * Print a proof for the equivalence of n1 and n2.
   *
   * @param term
   */
  virtual void printRewriteProof(std::ostream& os, const Node &n1, const Node &n2);

  // Return true if node prints as bool, false if it prints as a formula.
  virtual bool printsAsBool(const Node &n) {
    // Most nodes print as formulas, so this is the default.
    return false;
  }
};

class BooleanProof : public TheoryProof {
protected:
  ExprSet d_declarations; // all the boolean variables
public:
  BooleanProof(TheoryProofEngine* proofEngine);

  void registerTerm(Expr term) override;
};

class LFSCBooleanProof : public BooleanProof {
public:
  LFSCBooleanProof(TheoryProofEngine* proofEngine)
    : BooleanProof(proofEngine)
  {}
  void printOwnedTerm(Expr term,
                      std::ostream& os,
                      const ProofLetMap& map) override;
  void printOwnedSort(Type type, std::ostream& os) override;
  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printSortDeclarations(std::ostream& os, std::ostream& paren) override;
  void printTermDeclarations(std::ostream& os, std::ostream& paren) override;
  void printDeferredDeclarations(std::ostream& os,
                                 std::ostream& paren) override;
  void printAliasingDeclarations(std::ostream& os,
                                 std::ostream& paren,
                                 const ProofLetMap& globalLetMap) override;

  bool printsAsBool(const Node& n) override;
  void printConstantDisequalityProof(std::ostream& os,
                                     Expr c1,
                                     Expr c2,
                                     const ProofLetMap& globalLetMap) override;
};

} /* CVC4 namespace */

#endif /* __CVC4__THEORY_PROOF_H */
