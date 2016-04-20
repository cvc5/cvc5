/*********************                                                        */
/*! \file array_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

#include "expr/expr.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

//proof object outputted by TheoryARRAY
class ProofArray : public Proof {
private:
  Node toStreamRecLFSC(std::ostream& out, TheoryProof* tp,
                       theory::eq::EqProof* pf,
                       unsigned tb,
                       const LetMap& map);

  /** Merge tag for ROW applications */
  unsigned d_reasonRow;
  /** Merge tag for ROW1 applications */
  unsigned d_reasonRow1;
  /** Merge tag for EXT applications */
  unsigned d_reasonExt;
public:
  ProofArray(theory::eq::EqProof* pf) : d_proof(pf) {}
  //it is simply an equality engine proof
  theory::eq::EqProof *d_proof;
  void toStream(std::ostream& out);
  void toStreamLFSC(std::ostream& out, TheoryProof* tp, theory::eq::EqProof* pf, const LetMap& map);

  void registerSkolem(Node equality, Node skolem);

  void setRowMergeTag(unsigned tag);
  void setRow1MergeTag(unsigned tag);
  void setExtMergeTag(unsigned tag);
};

namespace theory {
namespace arrays{
class TheoryArrays;
} /* namespace CVC4::theory::arrays */
} /* namespace CVC4::theory */

typedef __gnu_cxx::hash_set<Type, TypeHashFunction > TypeSet;

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

  virtual void registerTerm(Expr term);
};

class LFSCArrayProof : public ArrayProof {
public:
  LFSCArrayProof(theory::arrays::TheoryArrays* arrays, TheoryProofEngine* proofEngine)
    : ArrayProof(arrays, proofEngine)
  {}

  virtual void printOwnedTerm(Expr term, std::ostream& os, const LetMap& map);
  virtual void printOwnedSort(Type type, std::ostream& os);
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren);
  virtual void printSortDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printTermDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printDeferredDeclarations(std::ostream& os, std::ostream& paren);
};


}/* CVC4 namespace */

#endif /* __CVC4__ARRAY__PROOF_H */
