/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Annotation proof generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ANNOTATION_PROOF_GENERATOR_H
#define CVC5__PROOF__ANNOTATION_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "proof/proof_generator.h"
#include "proof/trust_id.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;

/**
 * This class wraps proofs with an ANNOTATE step.
 */
class AnnotationProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  AnnotationProofGenerator(
      Env& env,
      context::Context* c = nullptr,
      const std::string& name = "AnnotationProofGenerator");
  ~AnnotationProofGenerator() override = default;

  /**
   * Register an annotation for fact.
   *
   * The child proof is obtained either from pg, or if pg is null, from the
   * trusted fallback identified by tid and targs.
   */
  void addAnnotation(Node fact,
                     ProofGenerator* pg,
                     const std::vector<Node>& args,
                     TrustId tid = TrustId::NONE,
                     const std::vector<Node>& targs = {});

  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  bool hasProofFor(Node fact) override;
  std::string identify() const override;

 private:
  struct AnnotationInfo
  {
    AnnotationInfo(ProofGenerator* pg,
                   const std::vector<Node>& args,
                   TrustId tid,
                   const std::vector<Node>& targs);

    /** The generator for the child proof, if any. */
    ProofGenerator* d_pg;
    /** The arguments for the ANNOTATE step. */
    std::vector<Node> d_args;
    /** Fallback trust identifier if d_pg is null. */
    TrustId d_tid;
    /** Additional arguments for the fallback trust step. */
    std::vector<Node> d_targs;
  };

  using NodeAnnotationInfoMap =
      context::CDHashMap<Node, std::shared_ptr<AnnotationInfo>>;

  /** Mapping from facts to their annotation information. */
  NodeAnnotationInfoMap d_annotations;
  /** Name for debugging. */
  std::string d_name;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ANNOTATION_PROOF_GENERATOR_H */
