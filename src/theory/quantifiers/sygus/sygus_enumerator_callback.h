/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_enumerator
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_ENUMERATOR_CALLBACK_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_ENUMERATOR_CALLBACK_H

#include <unordered_set>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/extended_rewrite.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class ExampleEvalCache;
class SygusStatistics;
class SygusSampler;
class TermDbSygus;

/**
 * Class for callbacks in the fast enumerator. This class provides custom
 * criteria for whether or not enumerated values should be considered.
 */
class SygusEnumeratorCallback : protected EnvObj
{
 public:
  SygusEnumeratorCallback(Env& env,
                          TermDbSygus* tds = nullptr,
                          SygusStatistics* s = nullptr,
                          ExampleEvalCache* eec = nullptr);
  virtual ~SygusEnumeratorCallback() {}

  /**
   * Add term, return true if the term should be considered in the enumeration.
   * Notice that returning false indicates that n should not be considered as a
   * subterm of any other term in the enumeration.
   *
   * @param n The SyGuS term
   * @param bterms The (rewritten, builtin) terms we have already enumerated
   * @return true if n should be considered in the enumeration.
   */
  bool addTerm(const Node& n, std::unordered_set<Node>& bterms);

 protected:
  /** Get the cache value for the given candidate */
  virtual Node getCacheValue(const Node& n, const Node& bn);
  /**
   * Callback-specific add term
   *
   * @param n The SyGuS term
   * @param bn The builtin version of the enumerated term
   * @param bnr The (extended) rewritten form of bn
   * @return true if the term should be considered in the enumeration.
   */
  bool addTermInternal(const Node& n, const Node& bn, const Node& cval);
  /** Term database sygus */
  TermDbSygus* d_tds;
  /** pointer to the statistics */
  SygusStatistics* d_stats;
  /**
   * Pointer to the example evaluation cache utility (used for symmetry
   * breaking).
   */
  ExampleEvalCache* d_eec;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_ENUMERATOR_CALLBACK_H */
