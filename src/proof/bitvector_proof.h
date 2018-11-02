/*********************                                                        */
/*! \file bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof base class
 **
 ** Contains code (e.g. proof printing code) which is common to all bitvector
 *proofs.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITVECTOR_PROOF_H
#define __CVC4__BITVECTOR_PROOF_H

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "expr/expr.h"
#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "theory/bv/bitblast/bitblaster.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

typedef std::unordered_set<Expr, ExprHashFunction> ExprSet;
typedef std::unordered_map<Expr, ClauseId, ExprHashFunction> ExprToClauseId;
typedef std::unordered_map<Expr, unsigned, ExprHashFunction> ExprToId;
typedef std::unordered_map<Expr, Expr, ExprHashFunction> ExprToExpr;
typedef std::unordered_map<Expr, std::string, ExprHashFunction> ExprToString;

/**
 * A bitvector proof is best understood as having
 *
 *    1. A declaration of a "bitblasted formulas" -- boolean formulas
 *       that are each translations of a BV-literal (a comparison between BVs).
 *
 *       (and a proof that each "bitblasted formula" is implied by the
 *       corresponding BV literal)
 *
 *    2. A declaration of a cnf formula equisatisfiable to the bitblasted
 *       formula
 *
 *       (and a proof that each clause is implied by some bitblasted formula)
 *
 *    3. A proof of UNSAT from the clauses.
 *
 * This class is responsible for 1 & 2. The proof of UNSAT is delegated to a
 * subclass.
 */
class BitVectorProof : public TheoryProof
{
 protected:
  BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine);
  virtual ~BitVectorProof(){};

  // Set of BV variables in the input. (e.g. "a" in [ a = 000 ] ^ [ a == 001 ])
  ExprSet d_declarations;

  // terms and formulas that are actually relevant to the proof
  ExprSet d_usedBB;

  ExprSet d_seenBBTerms;        // terms that need to be bit-blasted
  std::vector<Expr> d_bbTerms;  // order of bit-blasting

  /** atoms that need to be bit-blasted,
   * BV-literals -> (BV-literals <=> bool formula)
   * where a BV literal is a signed or unsigned comparison.
   */
  ExprToExpr d_bbAtoms;

  // map from Expr representing normalized lemma to ClauseId in SAT solver
  ExprToClauseId d_bbConflictMap;

  theory::bv::TBitblaster<Node>* d_bitblaster;

  /** In an LFSC proof the manifestation of this expression bit-level
   * representation will have a string name. This method returns that name.
   */
  std::string getBBTermName(Expr expr);

  /** A mapping from constant BV terms to identifiers that will refer to them in
   * an LFSC proof, if constant-letification is enabled.
   */
  std::map<Expr, std::string> d_constantLetMap;

  /** Should we introduced identifiers to refer to BV constant terms?  It may
   * reduce the textual size of a proof!
   */
  bool d_useConstantLetification;

  /** Temporary storage for the set of nodes in the bitblasted formula which
   * correspond to CNF variables eventually used in the proof of unsat on the
   * CNF formula
   */
  std::set<Node> d_atomsInBitblastingProof;

  /**
   * Prints out
   *   (a) a declaration of bit-level interpretations corresponding to bits in
   *       the input BV terms.
   *   (b) a proof that the each BV literal entails a boolean formula on
   *       bitof expressions.
   */
  void printBitblasting(std::ostream& os, std::ostream& paren);

  /**
   * The proof that the bit-blasted SAT formula is correctly converted to CNF
   */
  std::unique_ptr<CnfProof> d_cnfProof;

 public:
  void printOwnedTerm(Expr term,
                      std::ostream& os,
                      const ProofLetMap& map) override;

  void printOwnedSort(Type type, std::ostream& os) override;

  /**
   * Populate the d_atomsInBitblastingProof member.
   * See its documentation
   */
  virtual void calculateAtomsInBitblastingProof() = 0;

  /**
   * Read the d_atomsInBitblastingProof member.
   * See its documentation.
   */
  const std::set<Node>* getAtomsInBitblastingProof();

  void registerTermBB(Expr term);

  /**
   * Informs the proof that the `atom` predicate was bitblasted into the
   * `atom_bb` term.
   *
   * The `atom` term must be a comparison of bitvectors, and the `atom_bb` term
   * a boolean formula on bitof expressions
   */
  void registerAtomBB(Expr atom, Expr atom_bb);

  void registerTerm(Expr term) override;

  /**
   * This must be done before registering any terms or atoms, since the CNF
   * proof must reflect the result of bitblasting those
   */
  virtual void initCnfProof(prop::CnfStream* cnfStream, context::Context* ctx);

  CnfProof* getCnfProof() { return d_cnfProof.get(); }

  void setBitblaster(theory::bv::TBitblaster<Node>* bb);

 private:
  ExprToString d_exprToVariableName;

  ExprToString d_assignedAliases;
  std::map<std::string, std::string> d_aliasToBindDeclaration;
  std::string assignAlias(Expr expr);
  bool hasAlias(Expr expr);

  // Functions for printing various BV terms. Helpers for BV's `printOwnedTerm`
  void printConstant(Expr term, std::ostream& os);
  void printOperatorNary(Expr term, std::ostream& os, const ProofLetMap& map);
  void printOperatorUnary(Expr term, std::ostream& os, const ProofLetMap& map);
  void printPredicate(Expr term, std::ostream& os, const ProofLetMap& map);
  void printOperatorParametric(Expr term, std::ostream& os, const ProofLetMap& map);
  void printBitOf(Expr term, std::ostream& os, const ProofLetMap& map);

  /**
   * Prints the LFSC construction of a bblast_term for `term`
   */
  void printTermBitblasting(Expr term, std::ostream& os);

  /**
   * For a given BV-atom (a comparison), prints a proof that that comparison
   * holds iff the bitblasted equivalent of it holds.
   * Uses a side-condidition to do the bit-blasting.
   */
  void printAtomBitblasting(Expr term, std::ostream& os, bool swap);
  void printAtomBitblastingToFalse(Expr term, std::ostream& os);

  void printSortDeclarations(std::ostream& os, std::ostream& paren) override;
  void printTermDeclarations(std::ostream& os, std::ostream& paren) override;
  void printDeferredDeclarations(std::ostream& os,
                                 std::ostream& paren) override;
  void printAliasingDeclarations(std::ostream& os,
                                 std::ostream& paren,
                                 const ProofLetMap& globalLetMap) override;

  void printConstantDisequalityProof(std::ostream& os,
                                     Expr c1,
                                     Expr c2,
                                     const ProofLetMap& globalLetMap) override;
  void printRewriteProof(std::ostream& os,
                         const Node& n1,
                         const Node& n2) override;
};

}/* CVC4 namespace */

#endif /* __CVC4__BITVECTOR__PROOF_H */
