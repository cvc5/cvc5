/*********************                                                        */
/*! \file fun_def_process.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Pre-process step for admissible recursively defined functions
 **/

#include "cvc4_private.h"

#ifndef CVC4__QUANTIFIERS_FUN_DEF_PROCESS_H
#define CVC4__QUANTIFIERS_FUN_DEF_PROCESS_H

#include <map>
#include <vector>
#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {

/**
 * Attribute marked true for types that are used as abstraction types in
 * the algorithm below.
 */
struct AbsTypeFunDefAttributeId
{
};
typedef expr::Attribute<AbsTypeFunDefAttributeId, bool> AbsTypeFunDefAttribute;

namespace quantifiers {

//Preprocessing pass to allow finite model finding for admissible recursive function definitions
// For details, see Reynolds et al "Model Finding for Recursive Functions" IJCAR 2016
class FunDefFmf {
private:
  /** simplify formula
  * This is A_0 in Figure 1 of Reynolds et al "Model Finding for Recursive Functions".
  * The input of A_0 in that paper is a pair ( term t, polarity p )
  * The return value of A_0 in that paper is a pair ( term t', set of formulas X ).
  *
  * This function implements this such that :
  *   n is t
  *   pol/hasPol is p
  *   the return value is t'
  *   the set of formulas X are stored in "constraints"
  *
  * Additionally, is_fun_def is whether we are currently processing the top of a function defintion,
  * since this affects whether we process the head of the definition.
  */
  Node simplifyFormula( Node n, bool pol, bool hasPol, std::vector< Node >& constraints, Node hd, bool is_fun_def,
                        std::map< int, std::map< Node, Node > >& visited,
                        std::map< int, std::map< Node, Node > >& visited_cons );
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
  /** get constraints
   *
   * This computes constraints for the final else branch of A_0 in Figure 1
   * of Reynolds et al "Model Finding for Recursive Functions". The range of
   * the cache visited stores the constraint (if any) for each node.
   */
  void getConstraints(Node n,
                      std::vector<Node>& constraints,
                      std::map<Node, Node>& visited);
};


}
}
}

#endif
