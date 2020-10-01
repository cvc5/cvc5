/*********************                                                        */
/*! \file buffered_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof generator for buffered proof steps
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__BUFFERED_PROOF_GENERATOR_H
#define CVC4__EXPR__BUFFERED_PROOF_GENERATOR_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"
#include "expr/proof_step_buffer.h"

namespace CVC4 {

/**
 * The proof generator for buffered steps. This class is a context-dependent
 * mapping from formulas to proof steps. It does not generate ProofNodes until it
 * is asked to provide a proof for a given fact.
 */
class BufferedProofGenerator : public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofStep>, NodeHashFunction>
      NodeProofStepMap;

 public:
  BufferedProofGenerator(context::Context* c, ProofNodeManager* pnm);
  ~BufferedProofGenerator() {}
  /** add step
   * Unless the overwrite policy is ALWAYS it does not replace previously
   * registered steps (modulo (dis)equality symmetry).
   */
  bool addStep(Node fact,
               ProofStep ps,
               CDPOverwrite opolicy = CDPOverwrite::NEVER);
  /** Get proof for. It is robust to (dis)equality symmetry. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** identify */
  std::string identify() const override { return "BufferedProofGenerator"; }

 private:
  /** maps expected to ProofStep */
  NodeProofStepMap d_facts;
  /** the proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__BUFFERED_PROOF_GENERATOR_H */
