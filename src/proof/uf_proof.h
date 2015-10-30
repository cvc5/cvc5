/*********************                                                        */
/*! \file uf_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief UF proof
 **
 ** UF proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UF__PROOF_H
#define __CVC4__UF__PROOF_H

#include "expr/expr.h"
#include "proof/proof_manager.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

//proof object outputted by TheoryUF
class ProofUF : public Proof {
private:
  static Node toStreamRecLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, unsigned tb, const LetMap& map);
public:
  ProofUF( theory::eq::EqProof * pf ) : d_proof( pf ) {}
  //it is simply an equality engine proof
  theory::eq::EqProof * d_proof;
  void toStream(std::ostream& out);
  static void toStreamLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, const LetMap& map);
};

  
namespace theory {
namespace uf {
class TheoryUF;
}
}

typedef __gnu_cxx::hash_set<Type, TypeHashFunction > TypeSet;


class UFProof : public TheoryProof {
protected:
  TypeSet d_sorts;        // all the uninterpreted sorts in this theory
  ExprSet d_declarations; // all the variable/function declarations
  
public:
  UFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* proofEngine);

  virtual void registerTerm(Expr term);
};

class LFSCUFProof : public UFProof {
public:
  LFSCUFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* proofEngine)
    : UFProof(uf, proofEngine)
  {}
  virtual void printTerm(Expr term, std::ostream& os, const LetMap& map);
  virtual void printSort(Type type, std::ostream& os); 
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren);
  virtual void printDeclarations(std::ostream& os, std::ostream& paren);
};


}/* CVC4 namespace */

#endif /* __CVC4__UF__PROOF_H */
