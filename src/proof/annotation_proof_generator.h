/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The annotation proof generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ANNOTATION_PROOF_GENERATOR_H
#define CVC5__PROOF__ANNOTATION_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"

namespace cvc5::internal {

class ProofNodeManager;

/**
 * Base class for annotators. An annotator is a utility that implements a
 * simple transformation on proofs: `annotate` below.
 */
class Annotator
{
 public:
  Annotator() {}
  virtual ~Annotator() {}
  /**
   * Annotate the proof node. This must return a proof node that concludes the
   * same thing as p.
   */
  virtual std::shared_ptr<ProofNode> annotate(std::shared_ptr<ProofNode> p) = 0;
};

/**
 * Annotation proof generator, used to "wrap" proofs of other proof generators
 * via the annotate method above.
 */
class AnnotationProofGenerator : public ProofGenerator
{
  typedef context::CDHashMap<Node, std::pair<ProofGenerator*, Annotator*>>
      NodeExpMap;
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>> NodeProofNodeMap;

 public:
  AnnotationProofGenerator(ProofNodeManager* pnm,
                           context::Context* c = nullptr,
                           std::string name = "AnnotationProofGenerator");
  ~AnnotationProofGenerator() {}
  /** Get the proof for formula f. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Can we give the proof for formula f? */
  bool hasProofFor(Node f) override;
  /**
   * Set explanation for fact f, called when pg has a proof for f.
   *
   * @param f The fact proven by pg,
   * @param pg The proof generator that can prove f.
   * @param a The annotator that will annotate the proof of f, if necessary.
   */
  void setExplanationFor(Node f, ProofGenerator* pg, Annotator* a);
  /**
   * Transform trust node, will be annotated by the given annotator.
   */
  TrustNode transform(const TrustNode& trn, Annotator* a);
  /** identify */
  std::string identify() const override;

 protected:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** Name identifier */
  std::string d_name;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /**
   * A context-dependent map from formulas to a generator + annotation
   * pair, which will be used to generate the proof of formulas if asked.
   * We use the context provided to this class or otherwise d_context above.
   */
  NodeExpMap d_exps;
  /**
   * A context-dependent map from formulas to the proof nodes we have
   * returned in calls to getProofFor.
   */
  NodeProofNodeMap d_proofs;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ANNOTATION_PROOF_GENERATOR_H */
