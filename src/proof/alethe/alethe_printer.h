/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

#include "context/cdhashset.h"
#include "proof/alethe/alethe_let_binding.h"
#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof_node.h"
#include "proof/proof_node_updater.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace proof {

/** A callback for populating a let binder.
 *
 * This callback does not actually update the proof node, but rather just
 * considers the terms in the proof nodes for sharing. This is done in
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
 * The Alethe printer, which prints proof nodes in an Alethe proof, according to
 * the proof rules defined in alethe_proof_rule.h.
 *
 * It expects to print proof nodes that have been processed by the Alethe proof
 * post-processor.
 */
class AletheProofPrinter : protected EnvObj
{
 public:
  AletheProofPrinter(Env& env, AletheNodeConverter& anc);
  ~AletheProofPrinter() {}
  /**
   * Prints a proof node in the Alethe proof format
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
  /** The printing context */
  context::Context d_context;
  /** Assumptions in context */
  context::CDHashMap<Node, std::string> d_assumptionsMap;
  /** Printed steps in context */
  context::CDHashMap<ProofNode*, std::string> d_pfMap;

  /** Prints an Alethe proof node
   *
   * The printing is parameterized by a prefix to be used in the step ids, as
   * well as by the current id (which will be incremented after this proof node,
   * if it is fresh, is printed). The prefix is used to facilitate identifying
   * that steps are under a given anchor.
   *
   * @param out The stream to write to
   * @param prefix The prefix to be used in step ids.
   * @param id The current id being used for printing step ids
   * @param pfn The proof node to be printed
   * @param assumptionsMap Map from assumptions to their ids. Since these ids
   * are arbitrary symbols for assumptions (which could be defined using user
   * names), the map ranges over strings
   * @param pfMap Map from proof nodes to their ids
   */
  void printInternal(std::ostream& out,
                     const std::string& prefix,
                     size_t& id,
                     std::shared_ptr<ProofNode> pfn);

  /** Print term into stream
   *
   * The printing is done separately because it uses the let binder (d_lbind)
   * for converting the term before printing.
   *
   * @param out The stream to write to
   * @param n The node to be printed
   */
  void printTerm(std::ostream& out, TNode n);

  /** Print the id for the previously printed step/assumption of the given proof
   * node.
   *
   * @param out The stream to write to
   * @param pfn The proof node
   * @param assumptionsMap Map from assumptions to their ids
   * @param pfMap Map from proof nodes to their ids
   */
  void printStepId(std::ostream& out, std::shared_ptr<ProofNode> pfn);

  /** Print the step with respective id, premises and arguments.
   *
   * @param out The stream to write to
   * @param stepId The id of the step
   * @param pfArgs The arguments of this step
   * @param pfChildren The premises of this step
   * @param assumptionsMap Map from assumptions to their ids
   * @param pfMap Map from proof nodes to their ids
   */
  void printStep(std::ostream& out,
                 const std::string& stepId,
                 AletheRule arule,
                 const std::vector<Node>& pfArgs,
                 const std::vector<std::shared_ptr<ProofNode>>& pfChildren);

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
