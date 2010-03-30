/*********************                                                        */
/** symbol_table.h
 ** Original author: cconway
 ** Major contributors: dejan, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A symbol table for the parsers' use.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SYMBOL_TABLE_H
#define __CVC4__PARSER__SYMBOL_TABLE_H

#include <string>
#include <stack>

#include <ext/hash_map>

#include "util/Assert.h"

namespace CVC4 {
namespace parser {

struct StringHashFunction {
  size_t operator()(const std::string& str) const {
    return __gnu_cxx::hash<const char*>()(str.c_str());
  }
};

/**
 * Generic symbol table for looking up variables by name.
 */
template <class ObjectType>
class SymbolTable {

private:

  /** The name to expression bindings */
  typedef __gnu_cxx::hash_map<std::string, ObjectType, StringHashFunction>
  LookupTable;

  /** The table iterator */
  typedef typename LookupTable::iterator table_iterator;
  /** The table iterator */
  typedef typename LookupTable::const_iterator const_table_iterator;

  /** Bindings for the names */
  LookupTable d_nameBindings;

public:

  /**
   * Bind the name of the variable to the given expression. If the variable
   * has been bind before, this will redefine it until its undefined.
   */
  void bindName(const std::string& name, const ObjectType& obj) throw () {
    d_nameBindings[name] = obj;
    Assert(isBound(name), "Expected name to be bound!");
  }

  /**
   * Unbinds the last binding of the name to the expression.
   */
  void unbindName(const std::string& name) throw () {
    table_iterator find = d_nameBindings.find(name);
    if(find != d_nameBindings.end()) {
/*
      find->second.pop();
      if(find->second.empty()) {
*/
        d_nameBindings.erase(find);
/*      }*/
    }
  }

  /**
   * Returns the last binding expression of the name.
   * Requires the name to have a binding in the table.
   */
  ObjectType getObject(const std::string& name) throw () {
    table_iterator find = d_nameBindings.find(name);
    Assert(find != d_nameBindings.end());
    return find->second; /*.top()*/
  }

  /**
   * Returns true is name is bound to an expression.
   */
  bool isBound(const std::string& name) const throw () {
    const_table_iterator find = d_nameBindings.find(name);
    return (find != d_nameBindings.end());
  }
};

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SYMBOL_TABLE_H */
