/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The printer for the Eunoia format.
 */
#include <cstddef>
#include <memory>

#include "cvc5_private.h"

#ifndef CVC5__PROOF__EO_PROOF_PRINTER_H
#define CVC5__PROOF__EO_PROOF_PRINTER_H

#include <iostream>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node_algorithm.h"
#include "proof/eo/eo_list_node_converter.h"
#include "proof/eo/eo_node_converter.h"
#include "proof/eo/eo_print_channel.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "rewriter/rewrite_proof_rule.h"
#include "smt/env_obj.h"
#include "smt/proof_manager.h"

namespace cvc5::internal {

namespace printer {
namespace smt2 {
class Smt2Printer;
}
}  // namespace printer

namespace proof {

class EoPrinter : protected EnvObj
{
 public:
  EoPrinter(Env& env,
            BaseEoNodeConverter& atp,
            rewriter::RewriteDb* rdb,
            uint32_t letThresh = 2);
  ~EoPrinter() {}

  /**
   * Print the full proof pfn.
   * @param out The output stream.
   * @param pfn The proof node.
   * @param psm The scope mode, which determines whether there are outermost
   * scope to process in pfn. If this is the case, we print assume steps.
   * @param pii Information relating the assertions of pfn to the input, if
   * they differ. This is the case e.g. if definitions were expanded in the
   * assertions, in which case they are printed as macro definitions and the
   * assumptions are printed in their input form.
   */
  void print(std::ostream& out,
             std::shared_ptr<ProofNode> pfn,
             ProofScopeMode psm = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS,
             const ProofInputInfo* pii = nullptr);
  /**
   * Same as above, but with a Eunoia print channel.
   * @param out The output stream.
   * @param pfn The proof node.
   * @param psm The scope mode.
   * @param pii Information relating the assertions of pfn to the input, if
   * they differ.
   */
  void print(EoPrintChannelOut& out,
             std::shared_ptr<ProofNode> pfn,
             ProofScopeMode psm = ProofScopeMode::DEFINITIONS_AND_ASSERTIONS,
             const ProofInputInfo* pii = nullptr);
  /**
   * Print the proof, assuming that previous proofs have been printed on this
   * printer that have (partially) given the definition of subterms and
   * subproofs in pfn.
   * @param out The output stream.
   * @param pfn The proof node.
   */
  void printNext(EoPrintChannelOut& out, std::shared_ptr<ProofNode> pfn);

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
  static bool isHandledTheoryRewrite(const Options& opts,
                                     ProofRewriteRule id,
                                     const Node& n);
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
   * Eunoia node converter.
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
  void printProofInternal(EoPrintChannel* out,
                          const ProofNode* pn,
                          bool addToCache);
  /**
   * Helper for print. Prints a (dummy) step concluding the formula assumed by
   * pn, which is expected to be an application of ProofRule::ASSUME that is
   * the body of the proof we are printing. This ensures that proofs always end
   * with a step and not an assume command.
   *
   * @param aout The output channel to print to.
   * @param pn The (assumption) proof node that is the body of the proof.
   */
  void printAssumeBodyStep(EoPrintChannelOut& aout, const ProofNode* pn);
  /**
   * Called at preorder traversal of proof node pn. Prints (if necessary) to
   * out.
   */
  void printStepPre(EoPrintChannel* out, const ProofNode* pn);
  /**
   * Called at postorder traversal of proof node pn. Prints (if necessary) to
   * out.
   */
  void printStepPost(EoPrintChannel* out, const ProofNode* pn);
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
  /**
   * Print the declarations and definitions for the given definitions and
   * assertions of a proof.
   *
   * @param out The output stream.
   * @param definitions The definitions of the proof, which are printed as
   * ordinary definitions.
   * @param assertions The assertions of the proof.
   * @param macroDefs The definitions to print as macro definitions.
   * @param pii Information relating the assertions to the input, see print.
   * @return true if the definitions in macroDefs were printed as macro
   * definitions. This is false if a symbol in macroDefs cannot be defined as
   * a macro, in which case the assumptions of the proof should not be printed
   * in their input form.
   */
  bool printDeclarations(std::ostream& out,
                         const std::vector<Node>& definitions,
                         const std::vector<Node>& assertions,
                         const std::vector<Node>& macroDefs,
                         const ProofInputInfo* pii);
  /**
   * Return true if we can define the symbols with the given names as macros,
   * given that we print the given definitions and terms.
   *
   * This is false if a name is used by a sort we declare, since Eunoia has a
   * single namespace for symbols, in contrast to SMT-LIB, where sorts and
   * functions are in separate ones.
   *
   * @param names The names of the symbols we intend to define as macros.
   * @param definitions The definitions we print.
   * @param terms The terms we print declarations from.
   * @return true if the symbols can be defined as macros.
   */
  bool canDefineMacros(const std::unordered_set<std::string>& names,
                       const std::vector<Node>& definitions,
                       const std::vector<Node>& terms) const;
  /**
   * Print the definition def, which is an equality (= f t), as a Eunoia
   * define command, which is a macro. If t is a lambda, the definition is
   * printed with the parameters of that lambda, e.g. (= f (lambda (x) t')) is
   * printed as (define f ((x T)) t').
   *
   * @param out The output stream.
   * @param eprinter The printer to use for printing the command.
   * @param def The definition.
   */
  void printMacroDefinition(std::ostream& out,
                            const printer::smt2::Smt2Printer& eprinter,
                            const Node& def);
  /** Reference to the term processor */
  BaseEoNodeConverter& d_tproc;
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
  EoPrintChannelPre d_eletify;
  /** A cache for explicit type-of variables, for printing DSL_REWRITE steps */
  std::map<ProofRewriteRule, std::vector<Node>> d_explicitTypeOf;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__EO_PROOF_PRINTER_H */
