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
 * Rewrite proof rule class
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITE_PROOF_RULE__H
#define CVC5__REWRITER__REWRITE_PROOF_RULE__H

#include <string>
#include <vector>
#include <unordered_set>

#include "expr/nary_match_trie.h"
#include "expr/node.h"
#include "rewriter/rewrites.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * The definition of a (conditional) rewrite rule. An instance of this
 * class is generated for each DSL rule provided in the rewrite files. The
 * interface of this class is used by the proof reconstruction algorithm.
 */
class RewriteProofRule
{
 public:
  RewriteProofRule();
  /**
   * Initialize this rule.
   * @param id The identifier of this rule
   * @param userFvs The (user-provided) free variable list of the rule. This
   * is used only to track the original names of the arguments to the rule.
   * @param fvs The internal free variable list of the rule. Notice these
   * variables are normalized such that *all* proof rules use the same
   * variables, per type. In detail, the n^th argument left-to-right of a given
   * type T is the same for all rules. This is to facilitate parallel matching.
   * @param cond The conditions of the rule, normalized to fvs.
   * @param conc The conclusion of the rule, which is an equality of the form
   * (= t s), where t is specified as rewriting to s. This equality is
   * normalized to fvs.
   * @param context The term context for the conclusion of the rule. This is
   * non-null for all rules that should be applied to fixed-point. The context
   * is a lambda term that specifies the next position of the term to rewrite.
   */
  void init(DslPfRule id,
            const std::vector<Node>& userFvs,
            const std::vector<Node>& fvs,
            const std::vector<Node>& cond,
            Node conc,
            Node context);
  /** get id */
  DslPfRule getId() const;
  /** get name */
  const char* getName() const;
  /** Get user variable list */
  const std::vector<Node>& getUserVarList() const;
  /** Get variable list */
  const std::vector<Node>& getVarList() const;
  /** The context that the rule is applied in */
  Node getContext() const { return d_context; }
  /** Does this rule have conditions? */
  bool hasConditions() const;
  /** Get (declared) conditions */
  const std::vector<Node>& getConditions() const;
  /**
   * Get the conditions of the rule under the substitution { vs -> ss }.
   */
  bool getObligations(const std::vector<Node>& vs,
                      const std::vector<Node>& ss,
                      std::vector<Node>& vcs) const;
  /**
   * Check match, return true if h matches the head of this rule; notifies
   * the match notify object ntm.
   *
   * Note this method is not run as the main matching algorithm for rewrite
   * proof reconstruction, which considers all rules in parallel. This method
   * can be used for debugging matches of h against the head of this rule.
   */
  void getMatches(Node h, expr::NotifyMatch* ntm) const;
  /** Get conclusion of the rule */
  Node getConclusion() const;
  /** Get conclusion of the rule for the substituted terms ss */
  Node getConclusionFor(const std::vector<Node>& ss) const;

  /**
   * Is variable explicit? An explicit variable is one that does not occur
   * in a condition and thus its value must be specified in a proof
   * in languages that allow for implicit/unspecified hole arguments,
   * e.g. LFSC.
   */
  bool isExplicitVar(Node v) const;
  /**
   * Get list context. This returns the parent kind of the list variable v.
   * For example, for
   *   (define-rule bool-or-true ((xs Bool :list) (ys Bool :list))
   *      (or xs true ys) true)
   * The variable xs has list context `OR`.
   *
   * If v is in an ambiguous context, an exception will have been thrown
   * in the constructor of this class.
   *
   * This method returns UNDEFINED_KIND if there is no list context for v,
   * e.g. if v is not a list variable.
   */
  Kind getListContext(Node v) const;
  /** Was this rule marked as being applied to fixed point? */
  bool isFixedPoint() const;
  /** Is this rule in flat form? */
  bool isFlatForm() const;

 private:
  /** The id of the rule */
  DslPfRule d_id;
  /** The conditions of the rule */
  std::vector<Node> d_cond;
  /** The obligation generator formulas of the rule */
  std::vector<Node> d_obGen;
  /** The conclusion of the rule (an equality) */
  Node d_conc;
  /** Is the rule applied in some fixed point context? */
  Node d_context;
  /** Whether the rule is in flat form */
  bool d_isFlatForm;
  /** the ordered list of free variables, provided by the user */
  std::vector<Node> d_userFvs;
  /** the ordered list of free variables */
  std::vector<Node> d_fvs;
  /** number of free variables */
  size_t d_numFv;
  /**
   * The free variables that do not occur in the conditions. These cannot be
   * "holes" in a proof.
   */
  std::unordered_set<Node> d_noOccVars;
  /** The context for list variables (see expr::getListVarContext). */
  std::map<Node, Kind> d_listVarCtx;
  /** The match trie (for fixed point matching) */
  expr::NaryMatchTrie d_mt;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC4__REWRITER__REWRITE_PROOF_RULE__H */
