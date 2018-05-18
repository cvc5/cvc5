/*********************                                                        */
/*! \file sygus_eval_unfold.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_eval_unfold
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_EVAL_UNFOLD_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_EVAL_UNFOLD_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers/sygus/sygus_invariance.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDbSygus;
  
/** SygusEvalUnfold
 * 
 * This class implements techniques for eagerly unfolding sygus evaluation
 * functions. For example, given sygus datatype type corresponding to grammar:
 *   A -> 0 | 1 | A+A
 * whose evaluation function is eval_A, this class adds lemmas 
 */
class SygusEvalUnfold 
{
public:
  SygusEvalUnfold( TermDbSygus* tds );
  ~SygusEvalUnfold(){}
  /** register evaluation term 
   * 
   * This is called by TermDatabase, during standard effort calls 
   */
  void registerEvalTerm( Node n );
  /** register model value 
   * 
   */
  void registerModelValue( Node n, Node v, std::vector< Node >& exps, std::vector< Node >& terms, std::vector< Node >& vals );
 private:
  /** sygus term database associated with this utility */
  TermDbSygus* d_tds;
  /** the set of evaluation terms we have already processed */
  std::unordered_set<Node, NodeHashFunction> d_eval_processed;
  std::map< Node, std::map< Node, bool > > d_subterms;
  std::map< Node, std::vector< Node > > d_evals;
  std::map< Node, std::vector< std::vector< Node > > > d_eval_args;
  std::map< Node, std::vector< bool > > d_eval_args_const;
  std::map< Node, std::map< Node, unsigned > > d_node_mv_args_proc;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_EVAL_UNFOLD_H */
