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

#include "expr/node.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermPoolDomain
{
 public:
  /** initialize */
  void initialize();
  /** add node to pool */
  void add(Node n);
  /** The list in this pool */
  std::unordered_set<Node, NodeHashFunction> d_terms;
};

class TermPoolQuantInfo
{
 public:
  std::vector<Node> d_instAddToPool;
  std::vector<Node> d_skolemAddToPool;
};

/** Term pools
 */
class TermPools : public QuantUtil
{
 public:
  TermPools() {}
  ~TermPools() {}
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() override;
  /** register pool */
  void registerPool(Node p, const std::vector<Node>& initValue);

  /** get domain */
  TermPoolDomain& getDomain(Node p);

  /**
   * Process instantiation
   */
  void processInstantiation(Node q, const std::vector<Node>& terms);
  void processSkolemization(Node q, const std::vector<Node>& skolems);

 private:
  void processInternal(Node q, const std::vector<Node>& ts, bool isInst);
  /** add to pool */
  void addToPool(Node n, Node p);
  /** Maps pools to a domain */
  std::map<Node, TermPoolDomain> d_pools;
  /** Maps quantifiers to info */
  std::map<Node, TermPoolQuantInfo> d_qinfo;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_POOLS_H */
