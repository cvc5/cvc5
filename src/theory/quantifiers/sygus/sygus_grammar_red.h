/*********************                                                        */
/*! \file sygus_grammar_red.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_grammar_red
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class TermDbSygus;

/** SygusRedundantCons
 *
 * This class computes the subset of indices of the constructors of a sygus type
 * that are redundant. To use this class, first call initialize( qe, tn ),
 * where tn is a sygus tn. Then, use getRedundant and/or isRedundant to get the
 * indicies of the constructors of tn that are redundant.
 */
class SygusRedundantCons
{
 public:
  SygusRedundantCons() {}
  ~SygusRedundantCons() {}
  /** register type tn
   *
   * qe : pointer to the quantifiers engine,
   * tn : the (sygus) type to compute redundant constructors for
   */
  void initialize(QuantifiersEngine* qe, TypeNode tn);
  /** Get the indices of the redundant constructors of the register type */
  void getRedundant(std::vector<unsigned>& indices);
  /**
   * This function returns true if the i^th constructor of the registered type
   * is redundant.
   */
  bool isRedundant(unsigned i);

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
   *
   * For example, for grammar:
   *   A -> C > B | B < C | not D
   *   B -> x | y
   *   C -> 0 | 1 | C+C
   *   D -> B >= C
   * If A is register with this class, then we store may store { 0, 1, 0 },
   * noting that the second constructor of A can be simulated with the first.
   * Notice that the third constructor is not considered redundant.
   */
  std::vector<int> d_sygus_red_status;
  /**
   * Map from constructor indices to the generic term for that constructor,
   * where the generic term for a constructor is the (canonical) term returned
   * by a call to TermDbSygus::mkGeneric.
   */
  std::map<unsigned, Node> d_gen_terms;
  /**
   * Map from the rewritten form of generic terms for constructors of the
   * registered type to their corresponding constructor index.
   */
  std::map<Node, unsigned> d_gen_cons;
  /** get generic list
   *
   * This function constructs all well-typed variants of a term of the form
   *    op( x1, ..., xn )
   * where op is the builtin operator for dt[c], and xi = pre[i] for i=1,...,n.
   *
   * It constructs a list of terms of the form g * sigma, where sigma
   * is an automorphism on { x1...xn } such that for all xi -> xj in sigma,
   * the type for arguments i and j of dt[c] are the same. We store this
   * list of terms in terms.
   *
   * This function recurses on the arguments of g, index is the current argument
   * we are processing, and pre stores the current arguments of
   *
   * For example, for a sygus grammar
   *   A -> and( A, A, B )
   *   B -> false
   * passing arguments such that g=and( x1, x2, x3 ) to this function will add:
   *   and( x1, x2, x3 ) and and( x2, x1, x3 )
   * to terms.
   */
  void getGenericList(TermDbSygus* tds,
                      const DType& dt,
                      unsigned c,
                      unsigned index,
                      std::map<int, Node>& pre,
                      std::vector<Node>& terms);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H */
