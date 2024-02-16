/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_grammar_red
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H

#include <unordered_set>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "expr/sygus_grammar.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbSygus;

/** SygusRedundantCons
 *
 * This class computes the subset of indices of the constructors of a sygus type
 * that are redundant. To use this class, first call initialize( qe, tn ),
 * where tn is a sygus tn. Then, use getRedundant and/or isRedundant to get the
 * indicies of the constructors of tn that are redundant.
 */
class SygusRedundantCons : protected EnvObj
{
 public:
  SygusRedundantCons(Env& env) : EnvObj(env) {}
  ~SygusRedundantCons() {}
  /** Minimize grammar */
  void minimize(SygusGrammar& g);
 private:
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
  std::unordered_set<Node> getGenericList(const SygusGrammar& g,
                      const Node& r);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H */
