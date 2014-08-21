/*********************                                                        */
/*! \file bitvector_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector proof
 **
 ** Bitvector proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITVECTOR__PROOF_H
#define __CVC4__BITVECTOR__PROOF_H

#include <iostream>
#include <stdint.h>
#include <vector>
#include <set>
#include <ext/hash_map>
#include <ext/hash_set>
#include <sstream>
#include "expr/expr.h"
#include "proof/proof_manager.h"

namespace CVC4 {

namespace theory {
namespace bv{
class TheoryBV;
}
}

class BitVectorProof : public TheoryProof {
  SatProof* d_resolutionProof;
  CnfProof* d_cnfProof; 
  // TODO:  add proofs for all subtheories
public:
  BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine);
  
  virtual void registerTerm(Expr term) {}

  virtual void printTerm(Expr term, std::ostream& os) = 0;
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
  virtual void printBitblasting(std::ostream& os, std::ostream& paren) = 0; 
};

class LFSCBitVectorProof: public BitVectorProof {
public:
  LFSCBitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
    :BitVectorProof(bv, proofEngine)
  {}
  virtual void printTerm(Expr term, std::ostream& os);
  virtual void printSort(Type type, std::ostream& os);
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren);
  virtual void printDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printBitblasting(std::ostream& os, std::ostream& paren); 
}; 

}/* CVC4 namespace */

#endif /* __CVC4__BITVECTOR__PROOF_H */
