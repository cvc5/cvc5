/*********************                                                        */
/*! \file fun_def_process.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
  //defined functions to input sort
  std::map< Node, TypeNode > d_sorts;
  //defined functions to injections input -> argument elements
  std::map< Node, std::vector< Node > > d_input_arg_inj;
  //simplify
  Node simplifyFormula( Node n, bool pol, bool hasPol, std::vector< Node >& constraints, Node hd, int is_fun_def = 0 );
  //simplify term
  void simplifyTerm( Node n, std::vector< Node >& constraints );
public:
  FunDefFmf(){}
  ~FunDefFmf(){}

  void simplify( std::vector< Node >& assertions, bool doRewrite = false );
};


}
}
}

#endif
