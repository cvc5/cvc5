/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for monomials.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__ARITH_NL_COMPARE_PROOF_GEN_H
#define CVC5__THEORY__ARITH__NL__EXT__ARITH_NL_COMPARE_PROOF_GEN_H

#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class ArithNlCompareProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  ArithNlCompareProofGenerator(Env& env);
  virtual ~ArithNlCompareProofGenerator();
  /**
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
  /** Make literal */
  static Node mkLit(
      NodeManager* nm, Kind k, const Node& a, const Node& b, bool isAbsolute);
  /** */
  static void setCompareLit(NodeManager* nm,
                            Node olit,
                            Kind k,
                            const Node& a,
                            const Node& b,
                            bool isAbsolute);
  /** */
  static Node getCompareLit(const Node& olit);
  /** */
  static Kind decomposeCompareLit(const Node& lit,
                                  bool isAbsolute,
                                  std::vector<Node>& a,
                                  std::vector<Node>& b);
  /** */
  static Kind combineRelation(Kind k1, Kind k2);
  /** */
  static void addProduct(const Node& n, std::vector<Node>& vec);
  /** */
  static bool diffProduct(const std::vector<Node>& a,
                          const std::vector<Node>& b,
                          std::map<Node, size_t>& diff);
  /** */
  static void iterateWhile(const Node& a,
                           const std::vector<Node>& avec,
                           size_t& index);
  /** */
  static void iterateWhileCmp(const Node& a,
                              const std::vector<Node>& avec,
                              size_t& aindex,
                              const Node& b,
                              const std::vector<Node>& bvec,
                              size_t& bindex);
  /** */
  static void iterateWhileEq(const std::vector<Node>& avec,
                             size_t& aindex,
                             const std::vector<Node>& bvec,
                             size_t& bindex);
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL_MONOMIAL_H */
