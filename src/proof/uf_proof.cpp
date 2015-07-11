/*********************                                                        */
/*! \file uf_proof.cpp
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "proof/uf_proof.h"
#include "theory/uf/theory_uf.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;


void ProofUF::toStream(std::ostream& out) {
  Trace("theory-proof-debug") << "; Print UF proof..." << std::endl;
}

UFProof::UFProof(theory::uf::TheoryUF* uf, TheoryProofEngine* pe)
  : TheoryProof(uf, pe)
{}

void UFProof::registerTerm(Expr term) {
  // already registered
  if (d_declarations.find(term) != d_declarations.end())
    return;
  
  Type type = term.getType();
  if (type.isSort()) {
    // declare uninterpreted sorts
    d_sorts.insert(type);
  }
  
  if (term.getKind() == kind::APPLY_UF) {
    Expr function = term.getOperator();
    d_declarations.insert(function);
  }

  if (term.isVariable()) {
    d_declarations.insert(term);
  }
  
  // recursively declare all other terms
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    // could belong to other theories
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCUFProof::printTerm(Expr term, std::ostream& os, const LetMap& map) {
  Assert (Theory::theoryOf(term) == THEORY_UF);

  if (term.getKind() == kind::VARIABLE ||
      term.getKind() == kind::SKOLEM) {
    os << term;
    return; 
  }
  
  Assert (term.getKind() == kind::APPLY_UF);
  
  if(term.getType().isBoolean()) {
    os << "(p_app ";
  }
  Expr func = term.getOperator();
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    os << "(apply _ _ ";
  }
  os << func << " ";
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->printBoundTerm(term[i], os, map);
    os << ")";
  }
  if(term.getType().isBoolean()) {
    os << ")";
  }
}

void LFSCUFProof::printSort(Type type, std::ostream& os) {
  Assert (type.isSort());
  os << type <<" "; 
}

void LFSCUFProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) {
  os << " ;; UF Theory Lemma \n;;";
  for (unsigned i = 0; i < lemma.size(); ++i) {
    os << lemma[i] <<" "; 
  }
  os <<"\n";
  //os << " (clausify_false trust)";
  UFProof::printTheoryLemmaProof( lemma, os, paren );
}

void LFSCUFProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the sorts
  for (TypeSet::const_iterator it = d_sorts.begin(); it != d_sorts.end(); ++it) {
    os << "(% " << *it << " sort\n";
    paren << ")";
  }

  // declaring the terms
  for (ExprSet::const_iterator it = d_declarations.begin(); it != d_declarations.end(); ++it) {
    Expr term = *it;

    os << "(% " << ProofManager::sanitize(term) << " ";
    os << "(term ";

    Type type = term.getType();
    if (type.isFunction()) {
      std::ostringstream fparen;
      FunctionType ftype = (FunctionType)type;
      std::vector<Type> args = ftype.getArgTypes();
      args.push_back(ftype.getRangeType());
      os << "(arrow";
      for (unsigned i = 0; i < args.size(); i++) {
        Type arg_type = args[i];
        os << " " << arg_type;
        if (i < args.size() - 2) {
          os << " (arrow";
          fparen << ")";
        }
      }
      os << fparen.str() << "))\n";
    } else {
      Assert (term.isVariable());
      os << type << ")\n";
    }
    paren << ")";
  }
}

