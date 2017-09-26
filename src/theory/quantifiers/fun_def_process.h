/*********************                                                        */
/*! \file fun_def_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Pre-process step for admissible recursively defined functions
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

//Preprocessing pass to allow finite model finding for admissible recursive function definitions
// For details, see Reynolds et al "Model Finding for Recursive Functions" IJCAR 2016
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
  /** simplify, which does the following:
  * (1) records all top-level recursive function definitions in assertions,
  * (2) runs Figure 1 of Reynolds et al "Model Finding for Recursive Functions" 
  * IJCAR 2016 on all formulas in assertions based on the definitions from part (1),
  * which are Sigma^{dfn} in that paper.
  */
  void simplify( std::vector< Node >& assertions );
};


}
}
}

#endif
