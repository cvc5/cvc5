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
 * The printer for the AletheLF format.
 */
#include <cstddef>
#include <memory>

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALF_PROOF_PRINTER_H
#define CVC5__PROOF__ALF_PROOF_PRINTER_H

#include <iostream>

#include "context/cdhashmap.h"
#include "expr/node_algorithm.h"
#include "proof/alf/alf_list_node_converter.h"
#include "proof/alf/alf_node_converter.h"
#include "proof/alf/alf_print_channel.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "rewriter/rewrite_proof_rule.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace proof {

class AlfPrinter : protected EnvObj
{
 public:
  AlfPrinter(Env& env, BaseAlfNodeConverter& atp, rewriter::RewriteDb* rdb);
  ~AlfPrinter() {}

  /**
   * Print the full proof of assertions => false by pfn.
   * @param out The output stream.
   * @param pfn The proof node.
   */
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

  /**
   * Print proof rewrite rule name r to output stream out
   * @param out The output stream.
   * @param r The proof rewrite rule. This should be one of the proof rewrite
   * rules that corresponds to a RARE rewrite.
   */
  void printDslRule(std::ostream& out, ProofRewriteRule r);

 private:
  /** Return true if it is possible to trust the topmost application in pfn */
  bool isHandled(const ProofNode* pfn) const;
  /** Return true if id is handled as a theory rewrite for term n */
  bool isHandledTheoryRewrite(ProofRewriteRule id, const Node& n) const;
  /** Return if the equality is handled as a bitblast step */
  bool isHandledBitblastStep(const Node& eq) const;
  /**
   * Return true if it is possible to evaluate n using the evaluation side
   * condition in the ALF signature. Notice this requires that all subterms of n
   * are handled. This method is used for determining if an application of
   * ProofRule::EVALUATE can be applied.
   */
  bool canEvaluate(Node n) const;
  /**
   * Whether we support evaluating (str.in_re s r) for any constant string s.
   */
  bool canEvaluateRegExp(Node r) const;
  /* Returns the normalized name of the proof rule of pfn */
  std::string getRuleName(const ProofNode* pfn) const;

  //-------------
  /**
   * Select only those children required by the proof rule.
   */
  void getChildrenFromProofRule(
      const ProofNode* pn, std::vector<std::shared_ptr<ProofNode>>& children);
  /**
   * Add the arguments of proof node pn to args in the order in which they
   * should be printed. This also ensures the nodes have been converted via the
   * ALF node converter.
   */
  void getArgsFromProofRule(const ProofNode* pn, std::vector<Node>& args);
  /**
   * Helper for print. Prints the proof node using the print channel out. This
   * may either write the proof to an output stream or preprocess it.
   */
  void printProofInternal(AlfPrintChannel* out, const ProofNode* pn);
  /**
   * Called at preorder traversal of proof node pn. Prints (if necessary) to
   * out.
   */
  void printStepPre(AlfPrintChannel* out, const ProofNode* pn);
  /**
   * Called at postorder traversal of proof node pn. Prints (if necessary) to
   * out.
   */
  void printStepPost(AlfPrintChannel* out, const ProofNode* pn);
  /**
   * Allocate (if necessary) the identifier for an assume-push step for pn and
   * return the identifier. pn should be an application of ProofRule::SCOPE.
   */
  size_t allocateAssumePushId(const ProofNode* pn, const Node& a);
  /**
   * Allocate (if necessary) the identifier for an assume step for the
   * assumption for formula n and return the identifier. Note this identifier is
   * unique for each assumed formula, although multiple assumption proofs for n
   * may exist.
   */
  size_t allocateAssumeId(const Node& n, bool& wasAlloc);
  /**
   * Allocate (if necessary) the identifier for step
   */
  size_t allocateProofId(const ProofNode* pn, bool& wasAlloc);
  /** Print let list to output stream out */
  void printLetList(std::ostream& out, LetBinding& lbind);
  /** Reference to the term processor */
  BaseAlfNodeConverter& d_tproc;
  /** Assume id counter */
  size_t d_pfIdCounter;
  /** Mapping proofs to identifiers */
  std::map<const ProofNode*, size_t> d_pletMap;
  /**
   * Context for d_passumeMap, which is pushed and popped when we encounter
   * SCOPE proofs.
   */
  context::Context d_passumeCtx;
  /** Mapping assumed formulas to identifiers */
  context::CDHashMap<Node, size_t> d_passumeMap;
  /** The (dummy) type used for proof terms */
  TypeNode d_pfType;
  /** term prefix */
  std::string d_termLetPrefix;
  /** The false node */
  Node d_false;
  /** List node converter */
  AlfListNodeConverter d_ltproc;
  /** Pointer to the rewrite database */
  rewriter::RewriteDb* d_rdb;
  /** The DSL rules we have seen */
  std::unordered_set<ProofRewriteRule> d_dprs;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALF_PROOF_PRINTER_H */
