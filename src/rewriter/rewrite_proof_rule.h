/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * proof rewrite rule class
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
 * The level for a rewrite, which determines which proof signature they are a
 * part of.
 */
enum class Level
{
  NORMAL,
  EXPERT,
};

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
   * @param _level The level of the rewrite, which determines which proof
   * signature they should be added to (normal or expert).
   */
  void init(ProofRewriteRule id,
            const std::vector<Node>& userFvs,
            const std::vector<Node>& fvs,
            const std::vector<Node>& cond,
            Node conc,
            Node context,
            Level _level);
  /** get id */
  ProofRewriteRule getId() const;
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
  /**
   * Get (uninstantiated) conclusion of the rule.
   * @param includeContext If we should include the context of this rule (if
   * the RARE rule is given a "context" as described in the constructor).
   * @return The (uninstantiated) conclusion of the rule.
   */
  Node getConclusion(bool includeContext = false) const;
  /**
   * Get conclusion of the rule for the substituted terms ss for the variables
   * v = getVarList() of this rule.
   *
   * @param ss The terms to substitute in this rule. Each ss[i] is the same sort
   * as v[i] if v[i] is not a list variable, or is an SEXPR if v[i] is a list
   * variable,
   * @return the substituted conclusion of the rule.
   */
  Node getConclusionFor(const std::vector<Node>& ss) const;
  /**
   * Get conclusion of the rule for the substituted terms ss.
   * Additionally computes the "witness term" for each variable in the rule
   * which gives the corresponding term.
   * In particular, for each v[i] where v = getVarList(),
   * witnessTerms[i] is either:
   * (UNDEFINED_KIND, {t}), specifying that v -> t,
   * (k, {t1...tn}), specifying that v -> (<k> t1 ... tn).
   * Note that we don't construct (<k> t1 ... tn) since it may be illegal to
   * do so if e.g. k=or, and n=1 due to restrictions on the arity of Kinds.
   *
   * @param ss The terms to substitute in this rule. Each ss[i] is the same sort
   * as v[i] if v[i] is not a list variable, or is an SEXPR if v[i] is a list
   * variable,
   * @param witnessTerms The computed witness terms for each variable of this
   * rule.
   * @return the substituted conclusion of the rule.
   */
  Node getConclusionFor(
      const std::vector<Node>& ss,
      std::vector<std::pair<Kind, std::vector<Node>>>& witnessTerms) const;
  /**
   * @return the list of applications of Kind::TYPE_OF that appear in the
   * conclusion or a premise. These require special handling by the
   * printer.
   */
  std::vector<Node> getExplicitTypeOfList() const;
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
  /**
   * Get condition definitions given an application vs -> ss of this rule.
   * This is used to handle variables that do not occur in the left hand side
   * of rewrite rules and are defined in conditions of this rule.
   * @param vs The matched variables of this rule.
   * @param ss The terms to substitute in this rule for each vs.
   * @param dvs The variables for which a definition can now be inferred.
   * @param dss The terms that each dvs are defined as, for each dvs.
   */
  void getConditionalDefinitions(const std::vector<Node>& vs,
                                 const std::vector<Node>& ss,
                                 std::vector<Node>& dvs,
                                 std::vector<Node>& dss) const;
  /** Get the signature level for the rewrite rule */
  Level getSignatureLevel() const;

 private:
  /** The id of the rule */
  ProofRewriteRule d_id;
  /** The conditions of the rule */
  std::vector<Node> d_cond;
  /** The conclusion of the rule (an equality) */
  Node d_conc;
  /** Is the rule applied in some fixed point context? */
  Node d_context;
  /** The level */
  Level d_level;
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
  /** Maps variables to the term they are defined to be */
  std::map<Node, Node> d_condDefinedVars;
  /** The context for list variables (see expr::getListVarContext). */
  std::map<Node, Node> d_listVarCtx;
  /** The match trie (for fixed point matching) */
  expr::NaryMatchTrie d_mt;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__REWRITE_PROOF_RULE__H */
