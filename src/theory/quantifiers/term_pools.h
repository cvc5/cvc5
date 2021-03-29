/*********************                                                        */
/*! \file term_pools.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for term enumeration
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TERM_POOLS_H
#define CVC4__THEORY__QUANTIFIERS__TERM_POOLS_H

#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantifiersState;

/**
 * Information concerning a pool variable.
 */
class TermPoolDomain
{
 public:
   /** initialize, which clears the data below */
  void initialize();
  /** add node to this pool */
  void add(Node n);
  /** The list in this pool */
  std::vector<Node> d_terms;
  /** 
   * The list of terms on this round. This is cleared at the beginning of an
   * instantiation round. The members are unique modulo equality.
   */
  std::vector<Node> d_currTerms;
};

/**
 * Contains all annotations that pertain to pools for a given quantified
 * formula.
 */
class TermPoolQuantInfo
{
 public:
   /** initialize, which clears the data below */
  void initialize();
  /** Annotations of kind INST_ADD_TO_POOL */
  std::vector<Node> d_instAddToPool;
  /** Annotations of kind SKOLEM_ADD_TO_POOL */
  std::vector<Node> d_skolemAddToPool;
};

/**
 * Term pools, which tracks the values of "pools", which are used for
 * pool-based instantiation.
 */
class TermPools : public QuantifiersUtil
{
 public:
  TermPools(QuantifiersState& qs);
  ~TermPools() {}
  /** reset */
  bool reset(Theory::Effort e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override;
  /** register pool */
  void registerPool(Node p, const std::vector<Node>& initValue);
  /** get terms for pool */
  void getTermsForPool(Node p, std::vector<Node>& terms);

  /**
   * Process instantiation
   */
  void processInstantiation(Node q, const std::vector<Node>& terms);
  void processSkolemization(Node q, const std::vector<Node>& skolems);

 private:
  void processInternal(Node q, const std::vector<Node>& ts, bool isInst);
  /** reference to the quantifiers state */
  QuantifiersState& d_qs;
  /** Maps pools to a domain */
  std::map<Node, TermPoolDomain> d_pools;
  /** Maps quantifiers to info */
  std::map<Node, TermPoolQuantInfo> d_qinfo;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_POOLS_H */
