/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_PRINTER_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_PRINTER_H

#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_let_binding.h"
#include "proof/proof_node.h"
#include "proof/proof_node_updater.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace proof {

/** A callback for populating a let binder.
 *
 * This callback does not actually update the proof node, but rather just
 * consider the terms in the proof nodes for sharing. This is done in
 * `shouldUpdate`, which is called on every proof node and always returns false.
 */
class LetUpdaterPfCallback : public ProofNodeUpdaterCallback
{
 public:
  LetUpdaterPfCallback(AletheLetBinding& lbind);
  ~LetUpdaterPfCallback();
  void initializeUpdate();
  /** Analyze the given proof node and populate d_lbind with its terms.
   *
   * Always returns false. */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;

 protected:
  /** The let binder populated during the update. */
  AletheLetBinding& d_lbind;
};

/**
 * The Alethe printer, which prints proof nodes in a Alethe proof, according to
 * the proof rules defined in alethe_proof_rule.h.
 *
 * It expects to print proof nodes that have processed by the Alethe proof post
 * processor.
 */
class AletheProofPrinter : protected EnvObj
{
 public:
  AletheProofPrinter(Env& env, AletheNodeConverter& anc);
  ~AletheProofPrinter() {}
  /**
   * This method prints a proof node that has been transformed into the Alethe
   * proof format
   *
   * @param out The stream to write to
   * @param pfn The proof node to be printed
   * @param assertionNames Mapping between assertions and names, if they were
   * given by the user.
   */
  void print(std::ostream& out,
             std::shared_ptr<ProofNode> pfn,
             const std::map<Node, std::string>& assertionNames);

 private:
  /** Used for printing the proof node after the initial Alethe anchor has been
   * printed
   *
   * The initial anchor introduces the initial assumptions of the problem, which
   * correspond to the problem assertions.
   *
   * @param out The stream to write to
   * @param pfn The proof node to be printed
   * @param assumptionsMap Map from proof nodes to their ids. Since these ids
   * are arbitrary symbols for assumptions (which could be defined using user
   * names), the map ranges over strings. Note that since subproofs may not
   * refer to steps outside of them, this map is fresh for each subproof.
   * @param pfMap Map from proof nodes to their ids. Since the step ids are auto
   * generated, we rely on integers. As above, this map is fresh per subproof.
   * @param prefix The prefix to be used when printing ids. E.g., the prefix
   * "t19.t2." is used when we are under a subproof started at step "t19" and
   * another at "t2" without leaving the first subproof.
   */
  void printInternal(
      std::ostream& out,
      const std::string& prefix,
      size_t& id,
      std::shared_ptr<ProofNode> pfn,
      std::unordered_map<Node, std::string>& assumptionsMap,
      std::unordered_map<std::shared_ptr<ProofNode>, std::string>& pfMap);


  /** Print term into stream
   *
   * The printing is done separately because it uses the let binder (d_lbind)
   * for converting the term before printing.
   */
  void printTerm(std::ostream& out, TNode n);

  void printStepId(
      std::ostream& out,
      std::shared_ptr<ProofNode> pfn,
      std::unordered_map<Node, std::string>& assumptionsMap,
      std::unordered_map<std::shared_ptr<ProofNode>, std::string>& pfMap);

  /** The let binder for printing with sharing. */
  AletheLetBinding d_lbind;

  /** The Alethe node converter */
  AletheNodeConverter& d_anc;

  /** The callback used for computing the let binding. */
  std::unique_ptr<LetUpdaterPfCallback> d_cb;
};

}  // namespace proof

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALETHE__ALETHE_PROOF_PRINTER_H */
