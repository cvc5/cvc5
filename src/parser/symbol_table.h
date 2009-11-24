/*********************                                           -*- C++ -*-  */
/** symbol_table.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Extra state of the parser shared by the lexer and parser.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#include <string>
#include <list>
#include <vector>

#include "expr/expr.h"

namespace CVC4 {

class SymbolTable {
public:
  // FIXME: No definitions for Type yet
  // void defineType(const std::string&, const Type&);
  void defineVar(const std::string, const void*);
  void defineVarList(const std::list<std::string>*, const void*);
  void defineVarList(const std::vector<std::string>*, const void*);

  // Type& lookupType(const std::string&);
  Expr& lookupVar(const std::string*);
};

}
