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
#include "theory/uf/equality_engine.h"

namespace CVC4 {

//proof object outputted by TheoryARRAY
class ProofArray : public Proof {
private:
  static Node toStreamRecLFSC(std::ostream& out, TheoryProof* tp,
                              theory::eq::EqProof* pf,
                              unsigned tb,
                              const LetMap& map);

  std::hash_map<Node, Node, NodeHashFunction> d_nodeToSkolem;
public:
  ProofArray(theory::eq::EqProof* pf) : d_proof(pf) {}
  //it is simply an equality engine proof
  theory::eq::EqProof *d_proof;
  void toStream(std::ostream& out);
  static void toStreamLFSC(std::ostream& out, TheoryProof* tp, theory::eq::EqProof* pf, const LetMap& map);

  void registerSkolem(Node equality, Node skolem);
};

namespace theory {
namespace arrays{
class TheoryArrays;
}
}

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

  virtual void printTerm(Expr term, std::ostream& os, const LetMap& map);
  virtual void printSort(Type type, std::ostream& os);
  virtual void printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren);
  virtual void printDeclarations(std::ostream& os, std::ostream& paren);
  virtual void printDeferredDeclarations(std::ostream& os, std::ostream& paren);
};


}/* CVC4 namespace */

#endif /* __CVC4__ARRAY__PROOF_H */
