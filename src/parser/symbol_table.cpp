/*********************                                           -*- C++ -*-  */
/** symbol_table.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include <string>
#include <list>
#include <vector>

#include "expr/expr.h"
#include "parser/symbol_table.h"

namespace CVC4 {
namespace parser {

void SymbolTable::defineVar(const std::string, const void*) throw() {
  
}

void SymbolTable::defineVarList(const std::list<std::string>*, const void*) throw() {
}

void SymbolTable::defineVarList(const std::vector<std::string>*, const void*) throw() {
}

// Type& SymbolTable::lookupType(const std::string&);
Expr& SymbolTable::lookupVar(const std::string*) throw() {
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
