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
 * The printer for the AletheLF format.
 */
#include <cstddef>
#include <memory>

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALF_PROOF_PRINTER_H
#define CVC5__PROOF__ALF_PROOF_PRINTER_H

#include <iostream>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node_algorithm.h"
#include "proof/alf/alf_list_node_converter.h"
#include "proof/alf/alf_node_converter.h"
#include "proof/alf/alf_print_channel.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "rewriter/rewrite_proof_rule.h"
#include "smt/env_obj.h"
#include "smt/proof_manager.h"

namespace cvc5::internal {

namespace proof {

class AlfPrinter : protected EnvObj
{
 public:
  AlfPrinter(Env& env,
             BaseAlfNodeConverter& atp,
             rewriter::RewriteDb* rdb,
             uint32_t letThresh = 2);
  ~AlfPrinter() {}

  /**
   * Print the full proof pfn.
   * @param out The output stream.
   * @param pfn The proof node.
   * @param psm The scope mode, which determines whether there are outermost
   * scope to process in pfn. If this is the case, we print assume steps.
   */
  void print(std::ostream& out,
             std::shared_ptr<ProofNode> pfn,
             ProofScopeMode psm = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS);
  /**
   * Same as above, but with an alf print output channel.
   * @param out The output stream.
   * @param pfn The proof node.
   * @param psm The scope mode.
   */
  void print(AlfPrintChannelOut& out,
             std::shared_ptr<ProofNode> pfn,
             ProofScopeMode psm = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS);
  /**
   * Print the proof, assuming that previous proofs have been printed on this
   * printer that have (partially) given the definition of subterms and
   * subproofs in pfn.
   * @param out The output stream.
   * @param pfn The proof node.
   */
  void printNext(AlfPrintChannelOut& out, std::shared_ptr<ProofNode> pfn);

  /**
   * Print proof rewrite rule name r to output stream out
   * @param out The output stream.
   * @param r The proof rewrite rule. This should be one of the proof rewrite
   * rules that corresponds to a RARE rewrite.
   */
  void printDslRule(std::ostream& out, ProofRewriteRule r);
  /**
   * Get the let binding that is computed by calls to printing terms in this
   * class.
   */
  LetBinding* getLetBinding();

  /** Return true if it is possible to trust the topmost application in pfn */
  static bool isHandled(const Options& opts, const ProofNode* pfn);

 private:
  /** Return true if id is handled as a theory rewrite for term n */
  static bool isHandledTheoryRewrite(ProofRewriteRule id, const Node& n);
  /** Return if the equality is handled as a bitblast step */
  static bool isHandledBitblastStep(const Node& eq);
  /**
   * Return true if it is possible to evaluate n using the evaluation side
   * condition in the CPC signature. Notice this requires that all subterms of n
   * are handled. This method is used for determining if an application of
   * ProofRule::EVALUATE can be applied.
   */
  static bool canEvaluate(Node n);
  /**
   * Return true if it is possible to evaluate n using the distinct values side
   * condition in the CPC signature. Notice this requires that all subterms of n
   * are handled. This method is used for determining if an application of
   * ProofRule::DISTINCT_VALUES can be applied.
   */
  static bool isHandledDistinctValues(const Node& n);
  /**
   * Whether we support evaluating (str.in_re s r) for any constant string s.
   */
  static bool canEvaluateRegExp(Node r);
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
   *
   * @param out The output channel to print to.
   * @param pn The proof node to print.
   * @param addToCache If true, we add (subproofs) of pn to the cache and do
   * not print them with this method if they are encounted again.
   */
  void printProofInternal(AlfPrintChannel* out,
                          const ProofNode* pn,
                          bool addToCache);
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
  /**
   * The set of proof nodes we have already printed with this class, as
   * used by printProofInternal.
   */
  context::CDHashSet<const ProofNode*> d_alreadyPrinted;
  /** Mapping assumed formulas to identifiers */
  context::CDHashMap<Node, size_t> d_passumeMap;
  /** The (dummy) type used for proof terms */
  TypeNode d_pfType;
  /** term prefix */
  std::string d_termLetPrefix;
  /** The false node */
  Node d_false;
  /** */
  TypeNode d_absType;
  /** Pointer to the rewrite database */
  rewriter::RewriteDb* d_rdb;
  /** The empty vector */
  std::vector<Node> d_emptyVec;
  /** The let binding */
  LetBinding d_lbind;
  /** The let binding we are using (possibly null) */
  LetBinding* d_lbindUse;
  /** The letification channel. */
  AlfPrintChannelPre d_aletify;
  /** A cache for explicit type-of variables, for printing DSL_REWRITE steps */
  std::map<ProofRewriteRule, std::vector<Node>> d_explicitTypeOf;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALF_PROOF_PRINTER_H */
