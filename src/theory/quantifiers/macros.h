/*********************                                                        */
/*! \file macros.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Pre-process step for detecting quantifier macro definitions
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_MACROS_H
#define __CVC4__QUANTIFIERS_MACROS_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantifierMacros{
private:
  void process( Node n, bool pol, std::vector< Node >& args, Node f );
  bool containsOp( Node n, Node op );
  bool isMacroKind( Node n, bool pol );
  //map from operators to macro definition ( basis, definition )
  std::map< Node, std::pair< Node, Node > > d_macro_defs;
private:
  Node simplify( Node n );
public:
  QuantifierMacros(){}
  ~QuantifierMacros(){}

  void simplify( std::vector< Node >& assertions, bool doRewrite = false );
};

}
}
}

#endif
