/*********************                                                        */
/*! \file array_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Arrray proof
 **
 ** Arrau proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ARRAY__PROOF_H
#define __CVC4__ARRAY__PROOF_H

#include "expr/expr.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "theory/arrays/theory_arrays.h"

namespace CVC4 {

namespace theory {
namespace arrays{
class TheoryArrays;
} /* namespace CVC4::theory::arrays */
} /* namespace CVC4::theory */

class ArrayProof : public TheoryProof {
  // TODO: whatever goes in this theory
public:
  ArrayProof(theory::arrays::TheoryArrays* arrays, TheoryProofEngine* proofEngine)
    : TheoryProof(arrays, proofEngine)
  {}
  virtual void registerTerm(Expr term) {}
  
  virtual void printTerm(Expr term, std::ostream& os, const LetMap& map) = 0;
  virtual void printSort(Type type, std::ostream& os) = 0;
  /** 
   * Print a proof for the theory lemma. Must prove
   * clause representing lemma to be used in resolution proof.
   * 
   * @param lemma clausal form of lemma
   * @param os output stream
   */
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) = 0;
  /** 
   * Print the variable/sorts declarations for this theory.
   * 
   * @param os 
   * @param paren 
   */
  virtual void printDeclarations(std::ostream& os, std::ostream& paren) = 0;
};

class LFSCArrayProof : public ArrayProof {
public:
  LFSCArrayProof(theory::arrays::TheoryArrays* uf, TheoryProofEngine* proofEngine)
    : ArrayProof(uf, proofEngine)
  {}
  // TODO implement
  virtual void printTerm(Expr term, std::ostream& os, const LetMap& map) {}
  virtual void printSort(Type type, std::ostream& os) {}
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) {}
  virtual void printDeclarations(std::ostream& os, std::ostream& paren) {}

};


}/* CVC4 namespace */

#endif /* __CVC4__ARRAY__PROOF_H */
