/*********************                                                        */
/*! \file letify.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for computing letification
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LETIFY_H
#define CVC4__PROOF__LFSC__LETIFY_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {
namespace proof {

/**
 * Utilities for letification.
 */
class Letify
{
 public:
  //------------------- letification of proofs
  /**
   * Stores proofs in map that require letification, mapping them to a unique
   * identifier, allocated in pcounter. For store each proof node in the domain
   * of pletMap in the list pletList such that pletList[i] does not contain sub
   * proof pletList[j] for j>i.
   */
  static void computeProofLet(const ProofNode* pn,
                              std::vector<const ProofNode*>& pletList,
                              std::map<const ProofNode*, uint32_t>& pletMap,
                              uint32_t thresh = 2);
  /**
   * Compute the count of sub proof nodes in pn, store in pcount. Additionally,
   * store each proof node in the domain of pcount in an order in visitList
   * such that visitList[i] does not contain sub proof visitList[j] for j>i.
   */
  static void computeProofCounts(const ProofNode* pn,
                                 std::vector<const ProofNode*>& visitList,
                                 std::map<const ProofNode*, uint32_t>& pcount);
  /**
   * Convert a count to a let list
   */
  static void convertProofCountToLet(
      const std::vector<const ProofNode*>& visitList,
      const std::map<const ProofNode*, uint32_t>& pcount,
      std::vector<const ProofNode*>& pletList,
      std::map<const ProofNode*, uint32_t>& pletMap,
      uint32_t thresh = 2);
  //------------------- end letification of proofs
};

}  // namespace proof
}  // namespace CVC4

#endif
