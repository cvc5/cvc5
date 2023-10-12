/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The printer for the experimental AletheLF format.
 */
#include <cstddef>
#include <memory>

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF_PROOF_PRINTER_H
#define CVC4__PROOF__ALF_PROOF_PRINTER_H

#include <iostream>

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
  AlfPrinter(Env& env,
             AlfNodeConverter& atp,
             bool flatten,
             rewriter::RewriteDb* rdb);
  ~AlfPrinter() {}

  /**
   * Print the full proof of assertions => false by pfn.
   */
  void print(std::ostream& out, std::shared_ptr<ProofNode> pfn);

 private:
  /** Is handled? */
  bool isHandled(const ProofNode* pfn) const;
  bool canEvaluate(Node n) const;
  /* Returns the proof name normalized */
  static std::string getRuleName(const ProofNode* pfn);

  //-------------
  void getArgsFromProofRule(const ProofNode* pn, std::vector<Node>& args);
  void printProofInternal(AlfPrintChannel* out, const ProofNode* pn);
  void printStepPre(AlfPrintChannel* out, const ProofNode* pn);
  void printStepPost(AlfPrintChannel* out, const ProofNode* pn);
  /** Allocate assume id, return true if was newly allocated */
  size_t allocatePush(const ProofNode* pn);
  size_t allocateAssumeId(const Node& n, bool& wasAlloc);
  size_t allocateProofId(const ProofNode* pn, bool& wasAlloc);
  Node allocatePremise(size_t id);
  /** Print DSL rule */
  void printDslRule(std::ostream& out, rewriter::DslProofRule r);
  /** Print let list */
  void printLetList(std::ostream& out, LetBinding& lbind);
  /** The term processor */
  AlfNodeConverter& d_tproc;
  /** Assume id counter */
  size_t d_pfIdCounter;
  /** Mapping scope proofs to identifiers */
  std::map<const ProofNode*, size_t> d_ppushMap;
  /** Mapping proofs to identifiers */
  std::map<const ProofNode*, size_t> d_pletMap;
  /** Mapping assumed formulas to identifiers */
  std::map<Node, size_t> d_passumeMap;
  /** Mapping proof nodes to nodes (non-flatten) */
  std::map<const ProofNode*, Node> d_pnodeMap;
  std::map<size_t, Node> d_passumeNodeMap;
  TypeNode d_pfType;
  /** Active scopes */
  std::unordered_set<const ProofNode*> d_activeScopes;
  /** term prefix */
  std::string d_termLetPrefix;
  /** Flatten */
  bool d_proofFlatten;
  Node d_false;
  /** List node converter */
  AlfListNodeConverter d_ltproc;
  /** Pointer to the rewrite database */
  rewriter::RewriteDb* d_rdb;
  /** The DSL rules we have seen */
  std::unordered_set<rewriter::DslProofRule> d_dprs;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
