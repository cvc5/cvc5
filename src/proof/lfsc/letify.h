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

class Letify
{
 public:
  /**
   * Convert n to a form that is printed assuming definitions in letMap
   * with the given prefix.
   */
  static Node convert(Node n,
                      const std::map<Node, uint32_t>& letMap,
                      const std::string& prefix);
  //------------------- letification of terms
  /** stores nodes in map that require letification */
  static void computeLet(Node n,
                         std::vector<Node>& letList,
                         std::map<Node, uint32_t>& letMap,
                         uint32_t thresh = 2);
  /**
   * Compute the count of sub nodes in pn, store in pcount. Additionally,
   * store each node in the domain of pcount in an order in visitList
   * such that visitList[i] does not contain sub visitList[j] for j>i.
   */
  static void updateCounts(Node n,
                           std::vector<Node>& visitList,
                           std::map<Node, uint32_t>& count);
  /**
   * Same as above, for each node printed in proof pn
   */
  static void updateCounts(const ProofNode* pn,
                           std::vector<Node>& visitList,
                           std::map<Node, uint32_t>& count);
  /**
   * Convert a count to a let list
   */
  static void convertCountToLet(const std::vector<Node>& visitList,
                                const std::map<Node, uint32_t>& count,
                                std::vector<Node>& letList,
                                std::map<Node, uint32_t>& letMap,
                                uint32_t thresh = 2);
  //------------------- end letification of terms

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
