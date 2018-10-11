/*********************                                                        */
/*! \file bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Guy Katz, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof superclass
 **
 ** Contains code (e.g. proof printing code) which is common to all bitvector proofs.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITVECTOR__PROOF_H
#define __CVC4__BITVECTOR__PROOF_H



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

class BitVectorProof : public TheoryProof {
protected:
  BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine);
  virtual ~BitVectorProof() {};

  ExprSet d_declarations;

  ExprSet d_usedBB; // terms and formulas that are actually relevant to the proof

  ExprSet d_seenBBTerms; // terms that need to be bit-blasted
  std::vector<Expr> d_bbTerms; // order of bit-blasting
  ExprToExpr d_bbAtoms; // atoms that need to be bit-blasted

  // map from Expr representing normalized lemma to ClauseId in SAT solver
  ExprToClauseId d_bbConflictMap;

  theory::bv::TBitblaster<Node>* d_bitblaster;
  std::string getBBTermName(Expr expr);

  std::map<Expr,std::string> d_constantLetMap;
  bool d_useConstantLetification;

  std::set<Node> d_atomsInBitblastingProof;

  void printBitblasting(std::ostream& os, std::ostream& paren);

  CnfProof* d_cnfProof;

public:
  void printOwnedTerm(Expr term,
                      std::ostream& os,
                      const ProofLetMap& map) override;
  virtual void calculateAtomsInBitblastingProof() = 0;
  const std::set<Node>* getAtomsInBitblastingProof();
  void registerTermBB(Expr term);
  void registerAtomBB(Expr atom, Expr atom_bb);

  void registerTerm(Expr term) override;

  virtual void initCnfProof(prop::CnfStream* cnfStream, context::Context* ctx);
  void registerTrueUnit(prop::CnfStream* cnfStream, context::Context* ctx);
  void registerFalseUnit(prop::CnfStream* cnfStream, context::Context* ctx);
  CnfProof* getCnfProof() {return d_cnfProof; }

  void setBitblaster(theory::bv::TBitblaster<Node>* bb);

private:
  ExprToString d_exprToVariableName;

  ExprToString d_assignedAliases;
  std::map<std::string, std::string> d_aliasToBindDeclaration;
  std::string assignAlias(Expr expr);
  bool hasAlias(Expr expr);

  void printConstant(Expr term, std::ostream& os);
  void printOperatorNary(Expr term, std::ostream& os, const ProofLetMap& map);
  void printOperatorUnary(Expr term, std::ostream& os, const ProofLetMap& map);
  void printPredicate(Expr term, std::ostream& os, const ProofLetMap& map);
  void printOperatorParametric(Expr term, std::ostream& os, const ProofLetMap& map);
  void printBitOf(Expr term, std::ostream& os, const ProofLetMap& map);

  void printOwnedSort(Type type, std::ostream& os) override;
  void printTermBitblasting(Expr term, std::ostream& os);
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
