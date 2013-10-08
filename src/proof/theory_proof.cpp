/*********************                                                        */
/*! \file theory_proof.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "proof/theory_proof.h"

using namespace CVC4;

TheoryProof::TheoryProof()
  : d_atomSet()
{}
void TheoryProof::addAtom(Expr atom) {
  d_atomSet.insert(atom); 
  Assert (atom.getKind() == kind::EQUAL);
  addDeclaration(atom[0]);
  addDeclaration(atom[1]); 
}

void TheoryProof::addDeclaration(Expr term) {
  Type type = term.getType();
  if (type.isSort())
    d_sortDeclarations.insert(type);
  if (term.getKind() == kind::APPLY_UF) {
    Expr function = term.getOperator();
    d_termDeclarations.insert(function); 
  } else {
    Assert (term.isVariable()); 
    Assert (type.isSort()); 
    d_termDeclarations.insert(term);
  }
}

void LFSCTheoryProof::printTerm(Expr term, std::ostream& os) {
  if (term.isVariable()) {
    os << term; 
    return;
  }
  Assert (term.getKind() == kind::APPLY_UF);
  Expr func = term.getOperator();
  // only support unary functions so far
  Assert (func.getNumChildren() == 1); 
  os << "(apply _ _ " << func << " ";
  printTerm(term[0], os);
  os <<")"; 
}

void LFSCTheoryProof::printFormula(Expr atom, std::ostream& os) {
  // should make this more general 
  Assert (atom.getKind() == kind::EQUAL);
  os << "(= ";
  printTerm(atom[0], os);
  os << " ";
  printTerm(atom[1], os);
  os << ")"; 
}

void LFSCTheoryProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the sorts
  for (SortSet::const_iterator it = d_sortDeclarations.begin(); it != d_sortDeclarations.end(); ++it) {
    os << "(% " << *it << "sort \n";
    paren << ")"; 
  }

  // declaring the terms
  for (TermSet::const_iterator it = d_termDeclarations.begin(); it != d_termDeclarations.end(); ++it) {
    Expr term = *it;
    
    os << "(% " << term << "(term "; 
    paren <<")"; 

    Type type = term.getType();
    if (type.isFunction()) {
      FunctionType ftype = (FunctionType)type; 
      Assert (ftype.getArity() == 2);
      Type arg_type = ftype.getArgTypes()[0];
      Type result_type = ftype.getRangeType();
      os << "(arrow " << arg_type << " " << result_type << "))\n"; 
    } else {
      Assert (term.isVariable());
      Assert (type.isSort());
      os << type << ")\n";
    }
  }
} 
