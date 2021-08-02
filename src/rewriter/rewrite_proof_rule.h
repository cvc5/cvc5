/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include "expr/nary_match_trie.h"
#include "expr/node.h"
#include "rewriter/rewrites.h"

namespace cvc5 {
namespace rewriter {

/** Get DslPfRule from node */
bool getDslPfRule(TNode n, DslPfRule& id);

/**
 * The definition of a (conditional) rewrite rule.
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
   * @param isFixedPoint Whether the rule should be applied to fixed point in
   * the strategy
   * @param isFlatForm Whether the rule is the flat form of the actual rule
   * with the given id.
   */
  void init(DslPfRule id,
            const std::vector<Node>& userFvs,
            const std::vector<Node>& fvs,
            const std::vector<Node>& cond,
            Node conc,
            bool isFixedPoint,
            bool isFlatForm);
  /** get id */
  DslPfRule getId() const;
  /** get name */
  const char* getName() const;
  /** Get user variable list */
  const std::vector<Node>& getUserVarList() const;
  /** Get variable list */
  const std::vector<Node>& getVarList() const;
  /** Does this rule have conditions? */
  bool hasConditions() const;
  /** Get (declared) conditions */
  const std::vector<Node>& getConditions() const;
  /** Does this rule have side conditions? */
  bool hasSideConditions() const;
  /**
   * Get the conditions in context { vs -> ss }. This may involve running the
   * side conditions of this method.
   */
  bool getObligations(const std::vector<Node>& vs,
                      const std::vector<Node>& ss,
                      std::vector<Node>& vcs) const;
  /**
   * Check match, return true if h matches the head of this rule; notifies
   * the match notify object ntm.
   *
   * Note this method is not run as the main matching algorithm for rewrite
   * proof reconstruction, which considers all rules in parallel.
   */
  void getMatches(Node h, expr::NotifyMatch* ntm) const;
  /** Get conclusion of the rule */
  Node getConclusion() const;
  /** Get conclusion of the rule for ss */
  Node getConclusionFor(const std::vector<Node>& ss) const;

  /**
   * Is variable explicit? An explicit variable is one that does not occur
   * in a condition and thus its value must be specified in a proof.
   */
  bool isExplicitVar(Node v) const;
  /**
   * Get list context
   */
  Kind getListContext(Node v) const;
  /** Was this rule marked as being applied to fixed point? */
  bool isFixedPoint() const;
  /** Is this rule in flat form? */
  bool isFlatForm() const;

 private:
  /**
   * Purify side conditions from term n, store introduced side condition
   * applications into scs.
   */
  Node purifySideConditions(Node n, std::vector<Node>& scs);
  /**
   * Run side conditions in context { vs -> ss }, add the resulting conditions
   * to check into the vector vcs.
   */
  bool runSideConditions(const std::vector<Node>& vs,
                         const std::vector<Node>& ss,
                         std::vector<Node>& vcs) const;
  /** The id of the rule */
  DslPfRule d_id;
  /** The side conditions of the rule */
  std::vector<Node> d_scs;
  /** The conditions of the rule */
  std::vector<Node> d_cond;
  /** The obligation generator formulas of the rule */
  std::vector<Node> d_obGen;
  /** The conclusion of the rule (an equality) */
  Node d_conc;
  /** Is the rule applied until a fixed point is reached? */
  bool d_isFixedPoint;
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
  std::map<Node, bool> d_noOccVars;
  /** The context for list variables (see expr::getListVarContext). */
  std::map<Node, Kind> d_listVarCtx;
  /** The match trie (for fixed point matching) */
  expr::NaryMatchTrie d_mt;
};

}  // namespace rewriter
}  // namespace cvc5

#endif /* CVC4__REWRITER__REWRITE_PROOF_RULE__H */
