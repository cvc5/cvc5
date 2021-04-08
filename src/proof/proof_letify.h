/*********************                                                        */
/*! \file proof_letify.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for computing letification of proofs
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__PROOF_LETIFY_H
#define CVC4__PROOF__PROOF_LETIFY_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace cvc5 {
namespace proof {

/**
 * A callback which asks whether a proof node should be traversed for
 * proof letification. For example, this may make it so that SCOPE is not
 * traversed.
 */
class ProofLetifyTraverseCallback
{
 public:
  virtual ~ProofLetifyTraverseCallback() {}
  /**
   * Should we traverse proof node pn for letification? If this returns false,
   * then pn is being treated as a black box for letification.
   */
  virtual bool shouldTraverse(const ProofNode* pn);
};

/**
 * Utilities for letification.
 */
class ProofLetify
{
 public:
  //------------------- letification of proofs
  /**
   * Stores proofs in map that require letification, mapping them to a unique
   * identifier, allocated in pcounter. For store each proof node in the domain
   * of pletMap in the list pletList such that pletList[i] does not contain sub
   * proof pletList[j] for j>i.
   *
   * @param pn The proof node to letify
   * @param pletList The list of proofs occur in pn that should be letified
   * @param pletMap Mapping from proofs in pletList to an identifier
   * @param thresh The number of times a proof node has to occur to be added
   * to pletList
   * @param pltc A callback indicating whether to traverse a proof node during
   * this call.
   */
  static void computeProofLet(const ProofNode* pn,
                              std::vector<const ProofNode*>& pletList,
                              std::map<const ProofNode*, size_t>& pletMap,
                              size_t thresh = 2,
                              ProofLetifyTraverseCallback* pltc = nullptr);
  /**
   * Convert a count to a let list
   */
  static void convertProofCountToLet(
      const std::vector<const ProofNode*>& visitList,
      const std::map<const ProofNode*, size_t>& pcount,
      std::vector<const ProofNode*>& pletList,
      std::map<const ProofNode*, size_t>& pletMap,
      size_t thresh = 2);
  //------------------- end letification of proofs
 private:
  /**
   * Compute the count of sub proof nodes in pn, store in pcount. Additionally,
   * store each proof node in the domain of pcount in an order in visitList
   * such that visitList[i] does not contain sub proof visitList[j] for j>i.
   */
  static void computeProofCounts(const ProofNode* pn,
                                 std::vector<const ProofNode*>& visitList,
                                 std::map<const ProofNode*, size_t>& pcount,
                                 ProofLetifyTraverseCallback* pltc);
};

}  // namespace proof
}  // namespace cvc5

#endif
