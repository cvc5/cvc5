/*********************                                                        */
/*! \file macros.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
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
  void processAssertion( Node n );
  bool isBoundVarApplyUf( Node n );
  void process( Node n, bool pol, std::vector< Node >& args, Node f );
  bool contains( Node n, Node n_s );
  bool containsBadOp( Node n, Node op );
  bool isMacroLiteral( Node n, bool pol );
  void getMacroCandidates( Node n, std::vector< Node >& candidates );
  Node solveInEquality( Node n, Node lit );
  bool getFreeVariables( Node n, std::vector< Node >& v_quant, std::vector< Node >& vars, bool retOnly );
  bool getSubstitution( std::vector< Node >& v_quant, std::map< Node, Node >& solved,
                        std::vector< Node >& vars, std::vector< Node >& subs, bool reqComplete );
  //map from operators to macro basis terms
  std::map< Node, std::vector< Node > > d_macro_basis;
  //map from operators to macro definition
  std::map< Node, Node > d_macro_defs;
private:
  Node simplify( Node n );
public:
  QuantifierMacros(){}
  ~QuantifierMacros(){}

  bool simplify( std::vector< Node >& assertions, bool doRewrite = false );
};

}
}
}

#endif
