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
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrite_db_term_process.h"
#include "rewriter/rewrite_rcons.h"
#include "rewriter/rewrites.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/query_cache.h"
#include "util/statistics_stats.h"

namespace cvc5 {
namespace rewriter {

class RewriteDbProofCons
{
 public:
  RewriteDbProofCons(Env& env, RewriteDb* db);
  /**
   * Prove (= a b) with recursion limit recLimit. If cdp is provided, we add
   * a proove for this fact on it.
   */
  bool prove(CDProof* cdp,
             Node a,
             Node b,
             theory::TheoryId tid,
             MethodId mid,
             uint32_t recLimit);

 private:
  /** Notify class for the match trie */
  class RdpcMatchTrieNotify : public expr::NotifyMatch
  {
   public:
    RdpcMatchTrieNotify(RewriteDbProofCons& p) : d_parent(p) {}
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
  class ProvenInfo
  {
   public:
    ProvenInfo() : d_id(DslPfRule::FAIL), d_failMaxDepth(0) {}
    /** The identifier of the proof rule */
    DslPfRule d_id;
    /** The substitution */
    std::vector<Node> d_vars;
    std::vector<Node> d_subs;
    /** the maximum depth tried for rules that have failed */
    uint32_t d_failMaxDepth;
    /** The inflection conditions */
    std::vector<Node> d_iconds;
    /**
     * Is internal rule? these rules store children (if any) in d_vars.
     */
    bool isInternalRule() const { return isInternalDslPfRule(d_id); }
  };
  /** prove internal */
  DslPfRule proveInternal(Node eqi);
  /** prove internal */
  DslPfRule proveInternalViaStrategy(Node eqi);
  /** prove internal base eqi * { vars -> subs } */
  bool proveInternalBase(Node eqi, DslPfRule& id);
  /** ensure proof for proven fact exists in cdp */
  bool ensureProofInternal(CDProof* cdp, Node eqi);
  /** do evaluate */
  Node doEvaluate(Node n);
  /**
   * A notification that s is equal to n * { vars -> subs }. This function
   * should return false if we do not wish to be notified of further matches.
   */
  bool notifyMatch(Node s,
                   Node n,
                   std::vector<Node>& vars,
                   std::vector<Node>& subs);
  /** prove with rule */
  bool proveWithRule(DslPfRule id,
                     Node target,
                     const std::vector<Node>& vars,
                     const std::vector<Node>& subs,
                     bool doInflectMatch,
                     bool doFixedPoint,
                     bool doRecurse);
  /** get conclusion */
  Node getRuleConclusion(const RewriteProofRule& rpr,
                         const std::vector<Node>& vars,
                         const std::vector<Node>& subs,
                         ProvenInfo& pi,
                         bool doFixedPoint = false);
  /** Notify class for matches */
  RdpcMatchTrieNotify d_notify;
  /** Basic utility */
  TheoryRewriteRCons d_trrc;
  /** Node converter utility */
  RewriteDbNodeConverter d_rdnc;
  /** Pointer to rewrite database */
  RewriteDb* d_db;
  /** Pointer to proof node manager */
  ProofNodeManager* d_pnm;
  /** the evaluator utility */
  theory::Evaluator d_eval;
  /** currently proving */
  std::unordered_set<Node> d_currProving;
  /** cache for exists rule */
  std::unordered_map<Node, ProvenInfo> d_pcache;
  /** the evaluation cache */
  std::unordered_map<Node, Node> d_evalCache;
  /** common constants */
  Node d_true;
  Node d_false;
  /** current target */
  Node d_target;
  /** current recursion limit */
  uint32_t d_currRecLimit;
  /** current rule we are applying to fixed point */
  DslPfRule d_currFixedPointId;
  /** current conclusion from fixed point */
  Node d_currFixedPointConc;
  /** Total number of rewrites we were asked to prove */
  IntStat d_statTotalInputs;
  /** Total number of rewrites we tried to prove internally */
  IntStat d_statTotalAttempts;
  /** Total number of rewrites we proved successfully */
  IntStat d_statTotalInputSuccess;
  /** query cache, for simple disproving of goals */
  theory::quantifiers::QueryCache d_qcache;
};

}  // namespace rewriter
}  // namespace cvc5

#endif /* CVC5__THEORY__REWRITE_DB_PROOF_CONS__H */
