/*********************                                                        */
/*! \file macros.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantifierMacros{
private:
  QuantifiersEngine * d_qe;
private:
  bool d_ground_macros;
  bool processAssertion( Node n );
  bool isBoundVarApplyUf( Node n );
  bool process( Node n, bool pol, std::vector< Node >& args, Node f );
  bool containsBadOp( Node n, Node op, std::vector< Node >& opc, std::map< Node, bool >& visited );
  bool isMacroLiteral( Node n, bool pol );
  bool isGroundUfTerm( Node f, Node n );
  void getMacroCandidates( Node n, std::vector< Node >& candidates, std::map< Node, bool >& visited );
  Node solveInEquality( Node n, Node lit );
  bool getFreeVariables( Node n, std::vector< Node >& v_quant, std::vector< Node >& vars, bool retOnly, std::map< Node, bool >& visited );
  bool getSubstitution( std::vector< Node >& v_quant, std::map< Node, Node >& solved,
                        std::vector< Node >& vars, std::vector< Node >& subs, bool reqComplete );
  //map from operators to macro basis terms
  std::map< Node, std::vector< Node > > d_macro_basis;
  //map from operators to macro definition
  std::map< Node, Node > d_macro_defs;
  std::map< Node, Node > d_macro_defs_new;
  //operators to macro ops that contain them
  std::map< Node, std::vector< Node > > d_macro_def_contains;
  //simplify caches
  std::map< Node, Node > d_simplify_cache;
  std::map< Node, bool > d_quant_macros;
private:
  Node simplify( Node n );
  void addMacro( Node op, Node n, std::vector< Node >& opc );
  void debugMacroDefinition( Node oo, Node n );
public:
  QuantifierMacros( QuantifiersEngine * qe );
  ~QuantifierMacros(){}

  bool simplify( std::vector< Node >& assertions, bool doRewrite = false );
  void finalizeDefinitions();
};

}
}
}

#endif
