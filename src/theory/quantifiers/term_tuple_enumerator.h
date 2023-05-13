/******************************************************************************
 * Top contributors (to current version):
 *   Mikolas Janota, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of an enumeration of tuples of terms for the purpose
 * of quantifier instantiation.
 */
#ifndef CVC5__THEORY__QUANTIFIERS__TERM_TUPLE_ENUMERATOR_H
#define CVC5__THEORY__QUANTIFIERS__TERM_TUPLE_ENUMERATOR_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class Instantiate;
class TermPools;
class QuantifiersState;
class TermRegistry;
class RelevantDomain;

/**  Interface for enumeration of tuples of terms.
 *
 * The interface should be used as follows. Firstly, init is called, then,
 * repeatedly, verify if there are any combinations left by calling hasNext
 * and obtaining the next combination by calling next.
 *
 *  Optionally, if the  most recent combination is determined to be undesirable
 * (for whatever reason), the method failureReason is used to indicate which
 *  positions of the tuple are responsible for the said failure.
 */
class TermTupleEnumeratorInterface
{
 public:
  /** Initialize the enumerator. */
  virtual void init() = 0;
  /** Test if there are any more combinations. */
  virtual bool hasNext() = 0;
  /** Obtain the next combination, meaningful only if hasNext Returns true. */
  virtual void next(/*out*/ std::vector<Node>& terms) = 0;
  /** Record which of the terms obtained by the last call of next should not be
   * explored again. */
  virtual void failureReason(const std::vector<bool>& mask) = 0;
  virtual ~TermTupleEnumeratorInterface() = default;
};

/** A struct bundling up parameters for term tuple enumerator.*/
struct TermTupleEnumeratorEnv
{
  /**
   * Whether we should put full effort into finding an instantiation. If this
   * is false, then we allow for incompleteness, e.g. the tuple enumerator
   * may heuristically give up before it has generated all tuples.
   */
  bool d_fullEffort;
  /** Whether we increase tuples based on sum instead of max (see below) */
  bool d_increaseSum;
  /** Term registry */
  TermRegistry* d_tr;
};

/**  A function to construct a tuple enumerator.
 *
 * In the methods below, we support the enumerators based on the following idea.
 * The tuples are represented as tuples of
 * indices of  terms, where the tuple has as many elements as there are
 * quantified variables in the considered quantifier q.
 *
 * Like so, we see a tuple as a number, where the digits may have different
 * ranges. The most significant digits are stored first.
 *
 * Tuples are enumerated in a lexicographic order in stages. There are 2
 * possible strategies, either all tuples in a given stage have the same sum of
 * digits, or, the maximum over these digits is the same (controlled by
 * TermTupleEnumeratorEnv::d_increaseSum).
 *
 * In this method, the returned enumerator draws ground terms from the term
 * database (provided by td). The quantifiers state (qs) is used to eliminate
 * duplicates modulo equality.
 */
TermTupleEnumeratorInterface* mkTermTupleEnumerator(
    Node q, const TermTupleEnumeratorEnv* env, QuantifiersState& qs);
/** Same as above, but draws terms from the relevant domain utility (rd). */
TermTupleEnumeratorInterface* mkTermTupleEnumeratorRd(
    Node q, const TermTupleEnumeratorEnv* env, RelevantDomain* rd);

/** Make term pool enumerator */
TermTupleEnumeratorInterface* mkTermTupleEnumeratorPool(
    Node q, const TermTupleEnumeratorEnv* env, Node p);

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
#endif /* TERM_TUPLE_ENUMERATOR_H_7640 */
