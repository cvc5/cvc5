/*********************                                                        */
/*! \file uf_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief UF proof
 **
 ** UF proof
 **/

#include "cvc4_private.h"

#ifndef CVC4__UF__PROOF_H
#define CVC4__UF__PROOF_H

#include <memory>
#include <unordered_set>

#include "expr/expr.h"
#include "proof/theory_proof.h"
#include "theory/uf/equality_engine.h"
#include "util/proof.h"

namespace CVC4 {

// proof object outputted by TheoryUF
class ProofUF : public Proof
{
 public:
  ProofUF(std::shared_ptr<theory::eq::EqProof> pf) : d_proof(pf) {}
  void toStream(std::ostream& out) const override;
  void toStream(std::ostream& out, const ProofLetMap& map) const override;

 private:
  static void toStreamLFSC(std::ostream& out, TheoryProof* tp,
                           const theory::eq::EqProof& pf,
                           const ProofLetMap& map);
  static Node toStreamRecLFSC(std::ostream& out, TheoryProof* tp,
                              const theory::eq::EqProof& pf, unsigned tb,
                              const ProofLetMap& map);

  // it is simply an equality engine proof
  std::shared_ptr<theory::eq::EqProof> d_proof;
};

namespace theory {
namespace uf {
class TheoryUF;
}
}

typedef std::unordered_set<Type, TypeHashFunction > TypeSet;


class UFProof : public TheoryProof {
protected:
  TypeSet d_sorts;        // all the uninterpreted sorts in this theory
  ExprSet d_declarations; // all the variable/function declarations
  theory::TheoryId getTheoryId() override;

 public:
  UFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* proofEngine);

  void registerTerm(Expr term) override;
};

class LFSCUFProof : public UFProof {
public:
  LFSCUFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* proofEngine)
    : UFProof(uf, proofEngine)
  {}
  void printOwnedTermAsType(Expr term,
                            std::ostream& os,
                            const ProofLetMap& map,
                            TypeNode expectedType) override;
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


}/* CVC4 namespace */

#endif /* CVC4__UF__PROOF_H */
