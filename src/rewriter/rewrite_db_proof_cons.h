/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database proof reconstructor
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__REWRITE_DB_PROOF_CONS__H
#define CVC5__THEORY__REWRITE_DB_PROOF_CONS__H

#include <map>

#include "expr/match_trie.h"
#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "rewriter/basic_rewrite_rcons.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrite_db_term_process.h"
#include "rewriter/rewrite_proof_status.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "theory/evaluator.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * This class is used to reconstruct proofs of theory rewrites. It is described
 * in detail in the paper "Reconstructing Fine-Grained Proofs of Rewrites Using
 * a Domain-Specific Language", Noetzli et al FMCAD 2022.
 */
class RewriteDbProofCons : protected EnvObj
{
 public:
  RewriteDbProofCons(Env& env, RewriteDb* db);
  /**
   * Prove a = b with recursion limit recLimit and step limit stepLimit.
   * If cdp is provided, we add a proof for this fact on it.
   *
   * More specifically, the strategy used by this method is:
   * 1. Try to prove a=b via THEORY_REWRITE in context TheoryRewriteCtx::PRE_DSL,
   * 2. Try to prove a=b via a proof involving RARE rewrites,
   * 3. Try to prove a'=b' via a proof involving RARE rewrites, where a' and b'
   * are obtained by transforming a and b via RewriteDbNodeConverter.
   * 4. Try to prove a=b via THEORY_REWRITE in context
   * TheoryRewriteCtx::POST_DSL.
   *
   * The option --proof-granularity=dsl-rewrite-strict essentially moves step 1
   * after step 3, that is, RARE rewrites are always preferred to
   * THEORY_REWRITE.
   *
   * @param cdp The object to add the proof of (= a b) to.
   * @param a The left hand side of the equality.
   * @param b The right hand side of the equality.
   * @param recLimit The recursion limit for this call.
   * @param stepLimit The step limit for this call.
   * @param tmode Determines if/when to try THEORY_REWRITE.
   * @return true if we successfully added a proof of (= a b) to cdp
   */
  bool prove(CDProof* cdp,
             const Node& a,
             const Node& b,
             int64_t recLimit,
             int64_t stepLimit,
             TheoryRewriteMode tmode);

 private:
  /**
   * Preprocess closure equality. This is called at the beginning of prove to
   * simplify equalities between closures. In particular we apply two possible
   * simplifications:
   *
   * For (forall x P) = (forall x Q), we return P = Q, where a CONG step
   * is added to transform this step. That is, the proof is:
   *
   * P = Q
   * ----------------------------- CONG
   * (forall x. P) = (forall x. Q)
   *
   * where P = Q is left to prove.
   *
   * For (forall x. P) = (forall y. Q), we return
   * (forall y. P[y/x]) = (forall y. Q). If P[y/x] is not Q, the proof is:
   *
   * ----------------------- ALPHA_EQUIV
   * (forall x. P) = (forall y. P[y/x])   (forall y. P[y/x]) = (forall y. Q)
   * ----------------------------------------------------------------- TRANS
   *  (forall x. P) = (forall y. Q)
   *
   * where (forall y. P[y/x]) = (forall y. Q) is left to prove. If P[y/x] is Q,
   * the proof is:
   *
   * ----------------------------- ALPHA_EQUIV
   * (forall x. P) = (forall y. Q)
   *
   * where (forall y. Q) = (forall y. Q) is left to prove (trivially).
   *
   * In either case, we add a proof of (= a b) whose free assumptions are
   * either empty (if the returned equality is reflexive), or the returned
   * equality.
   */
  Node preprocessClosureEq(CDProof* cdp, const Node& a, const Node& b);
  /**
   * Notify class for the match trie, which is responsible for calling this
   * class to notify matches for heads of rewrite rules. It is used as a
   * callback to the match procedure in the trie maintained by this class.
   */
  class RdpcMatchTrieNotify : public expr::NotifyMatch
  {
   public:
    RdpcMatchTrieNotify(RewriteDbProofCons& p) : d_parent(p) {}
    /** Reference to the parent */
    RewriteDbProofCons& d_parent;
    /** notify the parent */
    bool notify(Node s,
                Node n,
                std::vector<Node>& vars,
                std::vector<Node>& subs) override
    {
      return d_parent.notifyMatch(s, n, vars, subs);
    }
  };
  /**
   * Proven info, which stores information for each equality we attempt to
   * prove, including whether we were successful and what is the maximum
   * depth we have tried if we have failed.
   */
  class ProvenInfo
  {
   public:
    ProvenInfo()
        : d_id(RewriteProofStatus::FAIL),
          d_dslId(ProofRewriteRule::NONE),
          d_failMaxDepth(-1)
    {
    }
    /** The identifier of the proof rule, or fail if we failed */
    RewriteProofStatus d_id;
    /** The identifier of the DSL proof rule if d_id is DSL */
    ProofRewriteRule d_dslId;
    /** The substitution used, if successful */
    std::vector<Node> d_vars;
    std::vector<Node> d_subs;
    /**
     * The maximum depth tried for rules that have failed, where -1 indicates
     * that the formula is unprovable at any depth.
     */
    int64_t d_failMaxDepth;
    /**
     * Is internal rule? these rules store children (if any) in d_vars.
     */
    bool isInternalRule() const
    {
      return d_id != RewriteProofStatus::DSL
             && d_id != RewriteProofStatus::THEORY_REWRITE;
    }
  };
  /**
   * Prove and store the proof of eq with internal form eqi in cdp if possible,
   * return true if successful. Tries the basic utility and all recursion depths
   * up to recLimit.
   *
   * @param cdp The object to add the proof of eq to.
   * @param eq The equality we are trying to prove.
   * @param eqi The internal version of the equality that may have been
   * converted from eq using d_rdnc.
   * @param recLimit The recursion limit for this call.
   * @param stepLimit The step limit for this call.
   * @param tmode Determines if/when to try THEORY_REWRITE.
   * @return true if we successfully added a proof of (= a b) to cdp
   */
  bool proveEqStratified(CDProof* cdp,
                         const Node& eq,
                         const Node& eqi,
                         int64_t recLimit,
                         int64_t stepLimit,
                         TheoryRewriteMode tmode);
  /**
   * Prove and store the proof of eq with internal form eqi in cdp if possible,
   * return true if successful. Tries a single recursion depth.
   *
   * @param cdp The object to add the proof of eq to.
   * @param eqi The equality we are trying to prove.
   * @param recLimit The recursion limit for this call.
   * @param stepLimit The step limit for this call.
   * @return true if we successfully added a proof of (= a b) to cdp
   */
  bool proveEq(CDProof* cdp,
               const Node& eqi,
               int64_t recLimit,
               int64_t stepLimit);
  /**
   * Prove internal, which is the main entry point for proven an equality eqi.
   * Returns the proof rule that was used to prove eqi, or
   * RewriteProofStatus::FAIL if we failed to prove.
   *
   * In detail, this runs a strategy of builtin tactics and otherwise consults
   * the rewrite rule database for the set of rewrite rules that match the
   * left hand side of eqi.
   *
   * If this call is successful (i.e. the returned rule is not
   * RewriteProofStatus::FAIL), the proven info for eqi is stored in
   * d_pcache[eqi].
   *
   * Note this method depends on the current step and recursion limits
   * d_currRecLimit/d_currStepLimit.
   */
  RewriteProofStatus proveInternal(const Node& eqi);
  /** Prove internal via strategy, a helper method for above. */
  RewriteProofStatus proveInternalViaStrategy(const Node& eqi);
  /**
   * Prove internal base eqi via DSL rule id.
   *
   * The purpose of this method is to prove or disprove eqi without using
   * recursion. If so, we store the rule used for eqi in its proven info
   * (d_pcache[eqi]). Notice that this method returns true if eqi is
   * proven or *disproven*, where in the latter case proven info has d_id
   * RewriteProofStatus::FAIL.
   */
  bool proveInternalBase(const Node& eqi, RewriteProofStatus& id);
  /**
   * Ensure proof for proven fact exists in cdp. This method is called on
   * equalities eqi after they have been successfully proven by this class.
   * Based on the information in proven infos, it constructs the formal
   * proof of eqi, which may involve recursing to premises of rules that
   * prove eqi. For details, see IV.B of Noetzli et al FMCAD 2022.
   *
   * @param cdp The proof to add the proof of eqi to
   * @param eqi The proven equality
   */
  bool ensureProofInternal(CDProof* cdp, const Node& eqi);
  /** Return the evaluation of n, which uses local caching. */
  Node doEvaluate(const Node& n);
  /**
   * Return the flattening of n. For example, this returns (+ a b c) for
   * (+ (+ a b) c). This method is used in the FLATTEN tactic.
   */
  Node doFlatten(const Node& n);
  /**
   * A notification that s is equal to n * { vars -> subs }. In this context,
   * s is the current left hand side of a term we are trying to prove and n is
   * the head of a rewrite rule.
   *
   * This method attempts to prove the current equality
   *
   * This function should return false if we do not wish to be notified of
   * further matches, e.g. if we successfully show a rewrite rule suffices to
   * prove the current equality d_target.
   */
  bool notifyMatch(const Node& s,
                   const Node& n,
                   std::vector<Node>& vars,
                   std::vector<Node>& subs);
  /**
   * Prove with rule, which attempts to prove the equality target using the
   * DSL proof rule id, which may be a builtin rule or a user-provided rule.
   *
   * @param id The rule to consider, which may be a DSL rule given by r if DSL.
   * @param target The equality to prove
   * @param vars The variables (arguments) of the proof rule
   * @param subs The substitution (instantiated arguments) of the proof rule
   * @param doTrans If true, then if we are trying to prove (= t s)
   * and the given rule proves (= t r), then we recursively try to prove
   * (= r s).
   * @param doFixedPoint If true, we consider the current rule applied to fixed
   * point
   * @param doRecurse Whether we should attempt to prove the rule when premises
   * are required, by making a recursive call to proveInternal.
   * @param r The DSL rule to consider if id is DSL.
   */
  bool proveWithRule(RewriteProofStatus id,
                     const Node& target,
                     const std::vector<Node>& vars,
                     const std::vector<Node>& subs,
                     bool doTrans,
                     bool doFixedPoint,
                     bool doRecurse,
                     ProofRewriteRule r = ProofRewriteRule::NONE);
  /**
   * Get conclusion of rewrite rule rpr under the current variable and
   * substitution. Store the information in proven info pi. If doFixedPoint
   * is true, apply the rule to fixed point.
   */
  Node getRuleConclusion(const RewriteProofRule& rpr,
                         const std::vector<Node>& vars,
                         const std::vector<Node>& subs,
                         ProvenInfo& pi,
                         bool doFixedPoint = false);
  /**
   * Rewrite concrete, which returns the result of rewriting n if it contains
   * no abstract subterms, or n itself otherwise.
   *
   * This method is required since the algorithm in this class often invokes
   * the rewriter as an oracle. We operate on terms with abstract subterms
   * in this class, and these terms should not be passed to the rewriter,
   * since the rewriter does not properly handle abstract subterms (for
   * instance, the BV theory rewriter assumes that all children of BV operators
   * have concrete bitwidths).
   */
  Node rewriteConcrete(const Node& n);
  /** Notify class for matches */
  RdpcMatchTrieNotify d_notify;
  /**
   * Basic utility for (user-independent) rewrite rule reconstruction. Handles
   * cases that should always be reconstructed, e.g. EVALUATE, REFL,
   * BETA_REDUCE.
   */
  BasicRewriteRCons d_trrc;
  /** Node converter utility */
  RewriteDbNodeConverter d_rdnc;
  /** Pointer to rewrite database */
  RewriteDb* d_db;
  /** the evaluator utility */
  theory::Evaluator d_eval;
  /** The set of equalities we are currently proving, to avoid loops */
  std::unordered_set<Node> d_currProving;
  /** Cache for the proven status of formulas */
  std::unordered_map<Node, ProvenInfo> d_pcache;
  /** the evaluation cache */
  std::unordered_map<Node, Node> d_evalCache;
  /** common constants */
  Node d_true;
  Node d_false;
  /** current target equality to prove */
  Node d_target;
  /** current recursion limit */
  int64_t d_currRecLimit;
  /** current step recursion limit */
  uint64_t d_currStepLimit;
  /** Did we fail due to a resource limit in the current run? */
  bool d_currFailResource;
  /** The mode for if/when to try theory rewrites */
  rewriter::TheoryRewriteMode d_tmode;
  /** current rule we are applying to fixed point */
  ProofRewriteRule d_currFixedPointId;
  /** current substitution from fixed point */
  std::vector<Node> d_currFixedPointSubs;
  /** current conclusion from fixed point */
  Node d_currFixedPointConc;
  /** Total number of rewrites we were asked to prove */
  IntStat d_statTotalInputs;
  /** Total number of rewrites we tried to prove internally */
  IntStat d_statTotalAttempts;
  /** Total number of rewrites we proved successfully */
  IntStat d_statTotalInputSuccess;
  /** Fixed point limit */
  static size_t s_fixedPointLimit;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__REWRITE_DB_PROOF_CONS__H */
