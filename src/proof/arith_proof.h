/*********************                                                        */
/*! \file arith_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arith proof
 **
 ** Arith proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ARITH__PROOF_H
#define __CVC4__ARITH__PROOF_H

#include "expr/expr.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

//proof object outputted by TheoryArith
class ProofArith : public Proof {
private:
  static Node toStreamRecLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, unsigned tb, const ProofLetMap& map);
public:
  ProofArith( theory::eq::EqProof * pf ) : d_proof( pf ) {}
  //it is simply an equality engine proof
  theory::eq::EqProof * d_proof;
  void toStream(std::ostream& out);
  static void toStreamLFSC(std::ostream& out, TheoryProof * tp, theory::eq::EqProof * pf, const ProofLetMap& map);
};


namespace theory {
namespace arith {
class TheoryArith;
}
}

typedef __gnu_cxx::hash_set<Type, TypeHashFunction > TypeSet;


class ArithProof : public TheoryProof {
protected:
  // std::map<Expr, std::string> d_constRationalString; // all the variable/function declarations

  //   TypeSet d_sorts;        // all the uninterpreted sorts in this theory
  ExprSet d_declarations; // all the variable/function declarations

  bool d_realMode;

public:
  ArithProof(theory::arith::TheoryArith* arith, TheoryProofEngine* proofEngine);

  virtual void registerTerm(Expr term);
};

class LFSCArithProof : public ArithProof {
public:
  LFSCArithProof(theory::arith::TheoryArith* arith, TheoryProofEngine* proofEngine)
    : ArithProof(arith, proofEngine)
  {}
  virtual void printOwnedTerm(Expr term, std::ostream& os, const ProofLetMap& map);
  virtual void printOwnedSort(Type type, std::ostream& os);
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren, const ProofLetMap& map);
  virtual void printSortDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printTermDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printDeferredDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printAliasingDeclarations(std::ostream& os, std::ostream& paren, const ProofLetMap &globalLetMap);
};


}/* CVC4 namespace */

#endif /* __CVC4__ARITH__PROOF_H */
