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
#include "proof/proof_manager.h"
using namespace CVC4;

TheoryProof::TheoryProof()
  : d_termDeclarations()
  , d_sortDeclarations()
  , d_declarationCache()
{}

void TheoryProof::addDeclaration(Expr term) {
  if (d_declarationCache.count(term)) {
    return;
  }

  Type type = term.getType();
  if (type.isSort())
    d_sortDeclarations.insert(type);
  if (term.getKind() == kind::APPLY_UF) {
    Expr function = term.getOperator();
    d_termDeclarations.insert(function);
  } else if (term.isVariable()) {
    //Assert (type.isSort() || type.isBoolean());
    d_termDeclarations.insert(term);
  }
  // recursively declare all other terms
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    addDeclaration(term[i]);
  }
  d_declarationCache.insert(term);
}

std::string toLFSCKind(Kind kind) {
  switch(kind) {
  case kind::OR : return "or";
  case kind::AND: return "and";
  case kind::XOR: return "xor";
  case kind::EQUAL: return "=";
  case kind::IFF: return "iff";
  case kind::IMPLIES: return "impl";
  case kind::NOT: return "not";
  default:
    Unreachable();
  }
}

void LFSCTheoryProof::printTerm(Expr term, std::ostream& os) {
  if (term.isVariable()) {
    if(term.getType().isBoolean()) {
      os << "(p_app " << term << ")";
    } else {
      os << term;
    }
    return;
  }

  switch(Kind k = term.getKind()) {
  case kind::APPLY_UF: {
    if(term.getType().isBoolean()) {
      os << "(p_app ";
    }
    Expr func = term.getOperator();
    for (unsigned i = 0; i < term.getNumChildren(); ++i) {
      os << "(apply _ _ ";
    }
    os << func << " ";
    for (unsigned i = 0; i < term.getNumChildren(); ++i) {
      printTerm(term[i], os);
      os << ")";
    }
    if(term.getType().isBoolean()) {
      os << ")";
    }
    return;
  }

  case kind::ITE:
    os << (term.getType().isBoolean() ? "(ifte " : "(ite _ ");
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << " ";
    printTerm(term[2], os);
    os << ")";
    return;

  case kind::EQUAL:
    os << "(";
    os << "= ";
    os << term[0].getType() << " ";
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << ")";
    return;

  case kind::DISTINCT:
    os << "(not (= ";
    os << term[0].getType() << " ";
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << "))";
    return;

  case kind::OR:
  case kind::AND:
  case kind::XOR:
  case kind::IFF:
  case kind::IMPLIES:
  case kind::NOT:
    // print the Boolean operators
    os << "(" << toLFSCKind(k);
    if(term.getNumChildren() > 2) {
      // LFSC doesn't allow declarations with variable numbers of
      // arguments, so we have to flatten these N-ary versions.
      std::ostringstream paren;
      os << " ";
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        printTerm(term[i], os);
        os << " ";
        if(i < term.getNumChildren() - 2) {
          os << "(" << toLFSCKind(k) << " ";
          paren << ")";
        }
      }
      os << paren.str() << ")";
    } else {
      // this is for binary and unary operators
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        os << " ";
        printTerm(term[i], os);
      }
      os << ")";
    }
    return;

  case kind::CONST_BOOLEAN:
    os << (term.getConst<bool>() ? "true" : "false");
    return;

  case kind::CHAIN: {
    // LFSC doesn't allow declarations with variable numbers of
    // arguments, so we have to flatten chained operators, like =.
    Kind op = term.getOperator().getConst<Chain>().getOperator();
    size_t n = term.getNumChildren();
    std::ostringstream paren;
    for(size_t i = 1; i < n; ++i) {
      if(i + 1 < n) {
        os << "(" << toLFSCKind(kind::AND) << " ";
        paren << ")";
      }
      os << "(" << toLFSCKind(op) << " ";
      printTerm(term[i - 1], os);
      os << " ";
      printTerm(term[i], os);
      os << ")";
      if(i + 1 < n) {
        os << " ";
      }
    }
    os << paren.str();
    return;
  }

  default:
    Unhandled(k);
  }

  Unreachable();
}

void LFSCTheoryProof::printAssertions(std::ostream& os, std::ostream& paren) {
  unsigned counter = 0;
  ProofManager::assertions_iterator it = ProofManager::currentPM()->begin_assertions();
  ProofManager::assertions_iterator end = ProofManager::currentPM()->end_assertions();

  // collect declarations first
  for(; it != end; ++it) {
    addDeclaration(*it);
  }
  printDeclarations(os, paren);

  it = ProofManager::currentPM()->begin_assertions();
  for (; it != end; ++it) {
    os << "(% A" << counter++ << " (th_holds ";
    printTerm(*it,  os);
    os << ")\n";
    paren << ")";
  }
}

void LFSCTheoryProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the sorts
  for (SortSet::const_iterator it = d_sortDeclarations.begin(); it != d_sortDeclarations.end(); ++it) {
    os << "(% " << *it << " sort\n";
    paren << ")";
  }

  // declaring the terms
  for (ExprSet::const_iterator it = d_termDeclarations.begin(); it != d_termDeclarations.end(); ++it) {
    Expr term = *it;

    os << "(% " << term << " ";
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
        //Assert (arg_type.isSort() || arg_type.isBoolean());
        os << " " << arg_type;
        if (i < args.size() - 2) {
          os << " (arrow";
          fparen << ")";
        }
      }
      os << fparen.str() << "))\n";
    } else {
      Assert (term.isVariable());
      //Assert (type.isSort() || type.isBoolean());
      os << type << ")\n";
    }
    paren << ")";
  }
}
