/*********************                                                        */
/*! \file theory_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for UfProofs.
 **
 ** A manager for UfProofs.
 **
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_PROOF_H
#define __CVC4__THEORY_PROOF_H

#include <ext/hash_set>
#include <iosfwd>

#include "expr/expr.h"
#include "util/proof.h"

namespace CVC4 {

  typedef __gnu_cxx::hash_set<Type, TypeHashFunction > SortSet;
  typedef __gnu_cxx::hash_set<Expr, ExprHashFunction > ExprSet;

  class TheoryProof {
  protected:
    ExprSet d_termDeclarations;
    SortSet d_sortDeclarations;
    ExprSet d_declarationCache;

  public:
    TheoryProof();
    virtual ~TheoryProof() {}
    virtual void printAssertions(std::ostream& os, std::ostream& paren) = 0;
    void addDeclaration(Expr atom);
  };

  class LFSCTheoryProof : public TheoryProof {
    void printDeclarations(std::ostream& os, std::ostream& paren);
  public:
    static void printTerm(Expr term, std::ostream& os);
    virtual void printAssertions(std::ostream& os, std::ostream& paren);
  };
} /* CVC4 namespace */

#endif /* __CVC4__THEORY_PROOF_H */
