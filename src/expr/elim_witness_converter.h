/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of witness elimination node conversion
 */
#include "cvc5_private.h"

#ifndef CVC5__EXPR__ELIM_WITNESS_NODE_CONVERTER_H
#define CVC5__EXPR__ELIM_WITNESS_NODE_CONVERTER_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

/**
 * Node converter to eliminate all terms of kind WITNESS. Each term replaced
 * in this way is captured by a skolem that witnesses the axiom for that
 * witness.
 *
 * Witness terms are required to track their justification as part of their
 * AST. In particular, it is required that all terms of kind WITNESS are given
 * an instantiation attribute of the form:
 *   (INST_ATTRIBUTE "witness" (SEXPR r a1 ... an))
 * where r is the (integer value of) a proof rule and a1...an are arguments
 * to that proof rule. This instantiation attribute is always constructed
 * assuming that ValidWitnessProofGenerator
 * (proof/valid_witness_proof_generator.h) is used to construct the witness
 * terms. These annotations are expected to be robust to rewriting and
 * substitution, e.g. rewriting (SEXPR r a1 ... an) does not change whether
 * it is a valid input to the definition of a proof rule. (Note this is not the
 * case for ProofRule::EXISTS_INV_CONDITION, which is why
 * ProofRule::MACRO_EXISTS_INV_CONDITION is used internally).
 *
 * For each witness of this form, we replace the witness by its corresponding
 * skolem and collect its corresponding axiom, defining what lemma we can
 * assume about it, which can be retrieved via ::getAxioms in this class.
 *
 * Note that we use WITNESS terms for two reasons:
 * (1) (witness x (= x t)) can naturally rewrite to t, which we wish to
 * infer when applicable by substitution + rewriting.
 * (2) witness terms trigger this class to recognize when axioms should be
 * added as lemmas. In other words, at the moment witness terms are
 * eliminated, we ensure their axiom is recorded as well.
 */
class ElimWitnessNodeConverter : protected EnvObj, public NodeConverter
{
 public:
  /** Eliminate witness terms.*/
  ElimWitnessNodeConverter(Env& env);
  ~ElimWitnessNodeConverter() {}
  /**
   * Convert node n as described above during post-order traversal.
   */
  Node postConvert(Node n) override;
  /**
   * Get the axioms
   */
  const std::vector<Node>& getAxioms() const;
  /**
   * Get the normal form of a quantified formula for which we are introducing
   * a skolem variable based on eliminating a witness term.
   */
  virtual Node getNormalFormFor(const Node& q);

 private:
  /** The list of axioms introduced by eliminating witness */
  std::vector<Node> d_axioms;
};

}  // namespace cvc5::internal

#endif
