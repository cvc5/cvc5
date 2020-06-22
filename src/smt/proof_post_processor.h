/*********************                                                        */
/*! \file proof_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PROOF_POST_PROCESSOR_H
#define CVC4__SMT__PROOF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"

namespace CVC4 {
namespace smt {

/**
 *
 */
class ProofPostProcessor
{
 public:
  ProofPostProcessor(ProofNodeManager* pnm);
  ~ProofPostProcessor() {}
  /**
   * Indicate that the given proof rule should be eliminated
   */
  void eliminate(PfRule rule);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** Kinds of proof rules we are eliminating */
  std::unordered_set<PfRule, PfRuleHashFunction> d_elimRules;
};

}  // namespace smt
}  // namespace CVC4

#endif
