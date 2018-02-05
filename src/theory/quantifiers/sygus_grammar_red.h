/*********************                                                        */
/*! \file sygus_grammar_red.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_grammar_red
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H
#define __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H

#include <map>
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusRedundantCons
 * 
 * This class computes the subset of indices of the constructors of a sygus type
 * that are redundant. To use this class, first call:
 *   initialize( qe, tn );
 * where tn is a sygus tn. Then, use getRedundant and/or isRedundant to get the
 * indicies of the constructors of tn that are redundant.
 */
class SygusRedundantCons 
{
public:
  SygusRedundantCons(){}
  ~SygusRedundantCons(){}
  /** register type tn 
   * 
   * qe : pointer to the quantifiers engine,
   * tn : the (sygus) type to compute redundant constructors for
   */
  void initialize( QuantifiersEngine * qe, TypeNode tn );
  /** Get the indices of the redundant constructors of the register type */
  void getRedundant( std::vector< unsigned >& indices );
  /** 
   * This function returns true if the i^th constructor of the registered type 
   * is redundant. 
   */
  bool isRedundant( unsigned i );  
private:
  /** the registered type */
  TypeNode d_type;
  /** redundant status 
   * 
   * For each constructor, status indicating whether the constructor is 
   * redundant, where:
   * 
   * 0 : not redundant,
   * 1 : redundant since another constructor can be used to construct values for 
   * this constructor.
   * 2 : redundant since there exists a term in the enumerator of the registered
   * type that is equivalent to terms of this constructor.
   * 
   * For example, for grammar:
   *   A -> C > B | B < C | not D
   *   B -> x | y
   *   C -> 0 | 1 | C+C
   *   D -> B >= C
   * If A is register with this class, then we store may store { 0, 1, 2 },
   * noting that the second constructor of A can be simulated with the first.
   * The third constructor has a values not ( B >= C ) which are equivalent to
   * the first constructor.
   * 
   * If the option sygusMinGrammarAgg() is not used, then we never compute the
   * value 2 in this vector.
   */ 
  std::vector< int > d_sygus_red_status;
  /** generic terms */
  std::map< Node, Node > d_gen_terms;
  /** generic redundant */
  std::map< Node, bool > d_gen_redundant;
  /** compute whether term g */
  bool computeRedundant( TypeNode tn, Node g );
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
