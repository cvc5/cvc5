/*********************                                                        */
/*! \file theory_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for UfProofs.
 **
 ** A manager for UfProofs.
 **
 ** 
 **/


#ifndef __CVC4__THEORY_PROOF_H
#define __CVC4__THEORY_PROOF_H

#include "cvc4_private.h"
#include "util/proof.h"
#include "expr/expr.h"
#include <ext/hash_set>
#include <iostream> 

namespace CVC4 {

  typedef __gnu_cxx::hash_set<Expr, ExprHashFunction > AtomSet;
  typedef __gnu_cxx::hash_set<Expr, ExprHashFunction > TermSet; 
  typedef __gnu_cxx::hash_set<Type, TypeHashFunction > SortSet; 
  
  class TheoryProof {
  protected:
    AtomSet d_atomSet;
    TermSet d_termDeclarations;
    SortSet d_sortDeclarations; 
    void addDeclaration(Expr atom); 
  public:
    TheoryProof();
    void addAtom(Expr atom); 
    virtual void printFormula(Expr atom, std::ostream& os) = 0;
    virtual void printDeclarations(std::ostream& os, std::ostream& paren) = 0; 
  };

  class LFSCTheoryProof: public TheoryProof {
    void printTerm(Expr term, std::ostream& os); 
  public:
    virtual void printFormula(Expr atom, std::ostream& os);
    virtual void printDeclarations(std::ostream& os, std::ostream& paren); 
  }; 
} /* CVC4 namespace */
#endif /* __CVC4__THEORY_PROOF_H */
