/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace theory {
namespace quantifiers {

class ExampleEvalCache;
class SygusStatistics;
class SygusSampler;
class TermDbSygus;

/**
 * Base class for callbacks in the fast enumerator. This allows a user to
 * provide custom criteria for whether or not enumerated values should be
 * considered.
 */
class SygusEnumeratorCallback : protected EnvObj
{
 public:
  SygusEnumeratorCallback(Env& env,
                          Node e,
                          TermDbSygus* tds = nullptr,
                          SygusStatistics* s = nullptr);
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
  virtual bool addTerm(Node n, std::unordered_set<Node>& bterms);

 protected:
  /**
   * Callback-specific notification of the above
   *
   * @param n The SyGuS term
   * @param bn The builtin version of the enumerated term
   * @param bnr The (extended) rewritten form of bn
   */
  virtual void notifyTermInternal(Node n, Node bn, Node bnr) {}
  /**
   * Callback-specific add term
   *
   * @param n The SyGuS term
   * @param bn The builtin version of the enumerated term
   * @param bnr The (extended) rewritten form of bn
   * @return true if the term should be considered in the enumeration.
   */
  virtual bool addTermInternal(Node n, Node bn, Node bnr) { return true; }
  /** The enumerator */
  Node d_enum;
  /** The type of enum */
  TypeNode d_tn;
  /** Term database sygus */
  TermDbSygus* d_tds;
  /** pointer to the statistics */
  SygusStatistics* d_stats;
};

class SygusEnumeratorCallbackDefault : public SygusEnumeratorCallback
{
 public:
  SygusEnumeratorCallbackDefault(Env& env,
                                 Node e,
                                 TermDbSygus* tds = nullptr,
                                 SygusStatistics* s = nullptr,
                                 ExampleEvalCache* eec = nullptr,
                                 SygusSampler* ssrv = nullptr,
                                 std::ostream* out = nullptr);
  virtual ~SygusEnumeratorCallbackDefault() {}

 protected:
  /** Notify that bn / bnr is an enumerated builtin, rewritten form of a term */
  void notifyTermInternal(Node n, Node bn, Node bnr) override;
  /** Add term, return true if n should be considered in the enumeration */
  bool addTermInternal(Node n, Node bn, Node bnr) override;
  /**
   * Pointer to the example evaluation cache utility (used for symmetry
   * breaking).
   */
  ExampleEvalCache* d_eec;
  /** sampler (for --sygus-rr-verify) */
  SygusSampler* d_samplerRrV;
  /** The output stream to print unsound rewrites for above */
  std::ostream* d_out;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_ENUMERATOR_CALLBACK_H */
