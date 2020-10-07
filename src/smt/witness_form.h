/*********************                                                        */
/*! \file witness_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for managing witness form conversion in proofs
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__WITNESS_FORM_H
#define CVC4__SMT__WITNESS_FORM_H

#include <unordered_set>

#include "expr/node_manager.h"
#include "expr/proof.h"
#include "expr/proof_generator.h"
#include "expr/term_conversion_proof_generator.h"

namespace CVC4 {
namespace smt {

/**
 * The witness form proof generator, which acts as a wrapper around a
 * TConvProofGenerator for adding rewrite steps for witness introduction.
 *
 * The proof steps managed by this class are stored in a context-independent
 * manager, which matches how witness forms are managed in SkolemManager.
 */
class WitnessFormGenerator : public ProofGenerator
{
 public:
  WitnessFormGenerator(ProofNodeManager* pnm);
  ~WitnessFormGenerator() {}
  /**
   * Get proof for, which expects an equality of the form t = toWitness(t).
   * This returns a proof based on the term conversion proof generator utility.
   * This proof may contain open assumptions of the form:
   *   k = toWitness(k)
   * Each of these assumptions are included in the set getWitnessFormEqs()
   * below after returning this call.
   */
  std::shared_ptr<ProofNode> getProofFor(Node eq) override;
  /** Identify */
  std::string identify() const override;
  /**
   * Does the rewrite require witness form conversion?
   * When calling this method, it should be the case that:
   *   Rewriter::rewrite(toWitness(t)) == Rewriter::rewrite(toWitness(s))
   * The rule MACRO_SR_PRED_TRANSFORM concludes t == s if the above holds.
   * This method returns false if:
   *   Rewriter::rewrite(t) == Rewriter::rewrite(s)
   * which means that the proof of the above fact does not need to do
   * witness form conversion to prove conclusions of MACRO_SR_PRED_TRANSFORM.
   */
  bool requiresWitnessFormTransform(Node t, Node s) const;
  /**
   * Same as above, with s = true. This is intended for use with
   * MACRO_SR_PRED_INTRO.
   */
  bool requiresWitnessFormIntro(Node t) const;
  /**
   * Get witness form equalities. This returns a set of equalities of the form:
   *   k = toWitness(k)
   * where k is a skolem, containing all rewrite steps used in calls to
   * getProofFor during the entire lifetime of this generator.
   */
  const std::unordered_set<Node, NodeHashFunction>& getWitnessFormEqs() const;

 private:
  /**
   * Convert to witness form. This internally constructs rewrite steps that
   * suffice to show t = toWitness(t) using the term conversion proof generator
   * of this class (d_tcpg).
   */
  Node convertToWitnessForm(Node t);
  /** The term conversion proof generator */
  TConvProofGenerator d_tcpg;
  /** The nodes we have already added rewrite steps for in d_tcpg */
  std::unordered_set<TNode, TNodeHashFunction> d_visited;
  /** The set of equalities added as proof steps */
  std::unordered_set<Node, NodeHashFunction> d_eqs;
  /** Lazy proof storing witness intro steps */
  LazyCDProof d_wintroPf;
};

}  // namespace smt
}  // namespace CVC4

#endif
