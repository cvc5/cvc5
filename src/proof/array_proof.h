/*********************                                                        */
/*! \file array_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arrray proof
 **
 ** Arrau proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ARRAY__PROOF_H
#define __CVC4__ARRAY__PROOF_H

#include <memory>
#include <unordered_set>

#include "expr/expr.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

// Proof object outputted by TheoryARRAY.
class ProofArray : public Proof {
 public:
  ProofArray(std::shared_ptr<theory::eq::EqProof> pf, unsigned row,
             unsigned row1, unsigned ext);

  void registerSkolem(Node equality, Node skolem);

  void toStream(std::ostream& out) const override;
  void toStream(std::ostream& out, const ProofLetMap& map) const override;

 private:
  void toStreamLFSC(std::ostream& out,
                    TheoryProof* tp,
                    const theory::eq::EqProof& pf,
                    const ProofLetMap& map) const;

  Node toStreamRecLFSC(std::ostream& out,
                       TheoryProof* tp,
                       const theory::eq::EqProof& pf,
                       unsigned tb,
                       const ProofLetMap& map) const;

  // It is simply an equality engine proof.
  std::shared_ptr<theory::eq::EqProof> d_proof;

  /** Merge tag for ROW applications */
  unsigned d_reasonRow;
  /** Merge tag for ROW1 applications */
  unsigned d_reasonRow1;
  /** Merge tag for EXT applications */
  unsigned d_reasonExt;
};

namespace theory {
namespace arrays{
class TheoryArrays;
} /* namespace CVC4::theory::arrays */
} /* namespace CVC4::theory */

typedef std::unordered_set<Type, TypeHashFunction > TypeSet;

class ArrayProof : public TheoryProof {
  // TODO: whatever goes in this theory
protected:
  TypeSet d_sorts;        // all the uninterpreted sorts in this theory
  ExprSet d_declarations; // all the variable/function declarations
  ExprSet d_skolemDeclarations; // all the skolem variable declarations
  std::map<Expr, std::string> d_skolemToLiteral;

public:
  ArrayProof(theory::arrays::TheoryArrays* arrays, TheoryProofEngine* proofEngine);

  std::string skolemToLiteral(Expr skolem);

  void registerTerm(Expr term) override;
};

class LFSCArrayProof : public ArrayProof {
public:
  LFSCArrayProof(theory::arrays::TheoryArrays* arrays, TheoryProofEngine* proofEngine)
    : ArrayProof(arrays, proofEngine)
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
};


}/* CVC4 namespace */

#endif /* __CVC4__ARRAY__PROOF_H */
