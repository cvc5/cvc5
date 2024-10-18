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

#include "smt/env_obj.h"
#include "proof/proof_generator.h"
#include "proof/conv_proof_generator.h"

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
  static Node mkLit(NodeManager* nm, Kind k, Node a, Node b, bool isAbsolute);
private:
  /** Converter for absolute value literals */
  TConvProofGenerator d_absConv;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL_MONOMIAL_H */
