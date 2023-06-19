/******************************************************************************
 * Top contributors (to current version):
 *   Vinícius Braga Freire, Diego Della Rocca de Camargos, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing dot proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__DOT__DOT_PRINTER_H
#define CVC5__PROOF__DOT__DOT_PRINTER_H

#include <iostream>
#include <stack>

#include "printer/let_binding.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace proof {

/**
 * An enumeration for proof nodes cluster type. Each type defines in which
 * cluster the proof node will be inserted when printed.
 */
enum class ProofNodeClusterType : uint8_t
{
  // ======== FIRST_SCOPE
  // Type of proof node cluster that is always in the root of the graph.
  // The rule is always SCOPE.
  FIRST_SCOPE = 0,
  // ======== SAT
  // Type of proof node cluster that is between FIRST_SCOPE and CNF.
  // The rules are: CHAIN_RESOLUTION, FACTORING, REORDERING, MACRO_RESOLUTION
  // and MACRO_RESOLUTION_TRUST.
  SAT,
  // ======== CNF
  // Type of proof node cluster that is below SAT and above THEORY_LEMMA or
  // PRE_PROCESSING.
  // The rules, that are described by the PfRule enumeration, are in the range
  // between NOT_NOT_ELIM and CNF_ITE_NEG3.
  CNF,
  // ======== THEORY_LEMMA
  // Proof nodes contained in a SCOPE which starts just after a SAT or CNF proof
  // cluster.
  THEORY_LEMMA,
  // ======== PRE_PROCESSING
  // Type of proof node cluster that is in the middle of the proof.
  // The rules can be of any type. The proof nodes that aren't THEORY_LEMMA
  // after CNF are PRE_PROCESSING. Therefore, the root of this cluster type
  // can't be a SCOPE proof node.
  PRE_PROCESSING,
  // ======== INPUT
  // Type of proof node that is always a leaf with regard to the FIRST_SCOPE.
  // The rules are always ASSUME and the argument assumed by it was only scoped
  // by the FIRST_SCOPE and no other SCOPE, i.e., it was not shadowed by an
  // inner scope.
  INPUT,
  // ======== NOT_DEFINED
  NOT_DEFINED
};

class DotPrinter : protected EnvObj
{
 public:
  DotPrinter(Env& env);
  ~DotPrinter();

  /**
   * Print the full proof of assertions => false by pn using the dot format.
   * @param out the output stream
   * @param pn the root node of the proof to print
   */
  void print(std::ostream& out, const ProofNode* pn);

 private:
  /**
   * Print the nodes of the proof in the format:
   * $NODE_ID [ label = "{$CONCLUSION|$RULE_NAME($RULE_ARGUMENTS)}", comment =
   * "{\"subProofQty\":$SUB_PROOF_QUANTITY}" ]; and then for each child of the
   * node $CHILD_ID -> $NODE_ID; and then recursively calls the function with
   * the child as argument.
   * @param out the output stream
   * @param pn the proof node to print
   * @param pfLetClosed the map from proof node hashs, of closed proof nodes, to
   * their printed ids
   * @param pfLetOpen the map, local to the current scope, of proof node hashs
   * to their printed ids
   * @param cfaMap the map from proof nodes to whether they contain assumptions
   * @param ancestorHashs a vector containing the hashs of all the proof nodes
   * ancestors traversed to get to pn
   * @param parentType the type of the parent node
   * @return the id of the proof node printed
   */
  uint64_t printInternal(std::ostream& out,
                         const ProofNode* pn,
                         std::map<size_t, uint64_t>& pfLetClosed,
                         std::map<size_t, uint64_t>& pfLetOpen,
                         std::unordered_map<const ProofNode*, bool>& cfaMap,
                         std::vector<size_t>& ancestorHashs,
                         ProofNodeClusterType parentType);

  /**
   * Print the nodes of the proof in the format:
   * $NODE_ID [ label = "{$CONCLUSION|$RULE_NAME($RULE_ARGUMENTS)}", comment =
   * "{\"subProofQty\":$SUB_PROOF_QUANTITY}" ];
   * @param out the output stream
   * @param pn the proof node to print
   */
  inline void printProofNodeInfo(std::ostream& out, const ProofNode* pn);

  /**
   * Return the arguments of a ProofNode
   * @param currentArguments an ostringstream that will store the arguments of
   * pn formatted as "$ARG[0], $ARG[1], ..., $ARG[N-1]"
   * @param pn a ProofNode
   */
  void ruleArguments(std::ostringstream& currentArguments, const ProofNode* pn);

  /** Add an escape character before special characters of the given string.
   * @param s The string to have the characters processed.
   * @return The string with the special characters escaped.
   */
  static std::string sanitizeString(const std::string& s);

  /** As above, but quotes are doubly escaped. */
  static std::string sanitizeStringDoubleQuotes(const std::string& s);

  /** Traverse proof node and populate d_subpfCounter, mapping each proof node
   * to the number of subproofs it contains, including itself
   *
   * @param pn the proof node to be traversed
   */
  void countSubproofs(const ProofNode* pn);

  /** Traverse proof node and populate d_lbind
   *
   * @param pn The proof node to be traversed
   */
  void letifyResults(const ProofNode* pn);

  /** Define the proof node type and populate d_nodesClusterType and
   * d_scopesArgs.
   * @param pn The proof node to categorize.
   * @param last The type of the parent of the current proof node
   * @return the current node type
   */
  ProofNodeClusterType defineProofNodeType(const ProofNode* pn,
                                           ProofNodeClusterType last);

  /** Whether the proof node is an input node or not. An input is a proof node
   * that has an ASSUME rule and the argument assumed by it must be scoped only
   * by the FIRST SCOPE. In other words, if there is at least one SCOPE (other
   * than the FIRST SCOPE) that is an ancestor of this ASSUME proof node and its
   * argument is scoped by this ancestor, then the ASSUME is no longer an input.
   * @param pn The proof node to be verified.
   * @return The bool indicating if the proof node is or not an input.
   */
  inline bool isInput(const ProofNode* pn);

  /** Verify if the rule is in the SAT range (i.e. a PfRule that is
   * CHAIN_RESOLUTION, FACTORING, REORDERING, MACRO_RESOLUTION or
   * MACRO_RESOLUTION_TRUST).
   * @param rule The rule to be verified.
   * @return The bool indicating if the rule is or not in the SAT range.
   */
  inline bool isSat(const PfRule& rule);

  /** Verify if the rule is in the CNF range (between NOT_NOT_ELIM and
   * CNF_ITE_NEG3) in the PfRule enumeration.
   * @param rule The rule to be verified.
   * @return The bool indicating if the rule is or not in the CNF range.
   */
  inline bool isCNF(const PfRule& rule);

  /** Verify if the rule is a SCOPE
   * @param rule The rule to be verified.
   * @return The bool indicating if the rule is or not a SCOPE.
   */
  inline bool isSCOPE(const PfRule& rule);

  /** Verify if the rule is in the theory lemma range (open interval between
   * CNF_ITE_NEG3 and LFSC_RULE) or if the rule is a SCOPE or THEORY_LEMMA.
   * @param rule The rule to be verified.
   * @return The bool indicating whether the rule is for a theory lemma
   * range.
   */
  inline bool isTheoryLemma(const PfRule& rule);

  /** Verify if the rule is an ASSUME
   * @param rule The rule to be verified.
   * @return The bool indicating if the rule is or not an ASSUME.
   */
  inline bool isASSUME(const PfRule& rule);

  /** All unique subproofs of a given proof node (counting itself). */
  std::map<const ProofNode*, size_t> d_subpfCounter;

  /** Let binder for terms in proof nodes */
  LetBinding d_lbind;

  /** Counter that indicates the current rule ID */
  uint64_t d_ruleID;

  /** The arguments (assumptions), per level, of all scopes under which the
   * traversal is currently under. */
  std::vector<std::reference_wrapper<const std::vector<Node>>> d_scopesArgs;

  /** All the subgraph description strings */
  std::vector<std::ostringstream> d_subgraphsStr;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
