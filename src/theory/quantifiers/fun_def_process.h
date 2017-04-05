/*********************                                                        */
/*! \file fun_def_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Pre-process steps for well-defined functions
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_FUN_DEF_PROCESS_H
#define __CVC4__QUANTIFIERS_FUN_DEF_PROCESS_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

//find finite models for well-defined functions
class FunDefFmf {
private:
  //simplify
  Node simplifyFormula( Node n, bool pol, bool hasPol, std::vector< Node >& constraints, Node hd, int is_fun_def,
                        std::map< int, std::map< Node, Node > >& visited,
                        std::map< int, std::map< Node, Node > >& visited_cons );
  //simplify term
  void simplifyTerm( Node n, std::vector< Node >& constraints, std::map< Node, bool >& visited );
public:
  FunDefFmf(){}
  ~FunDefFmf(){}
  //defined functions to input sort (alpha)
  std::map< Node, TypeNode > d_sorts;
  //defined functions to injections input -> argument elements (gamma)
  std::map< Node, std::vector< Node > > d_input_arg_inj;
  // (newly) defined functions
  std::vector< Node > d_funcs;
  //simplify
  void simplify( std::vector< Node >& assertions, bool doRewrite = false );
};


}
}
}

#endif
