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

#ifndef CVC4__THEORY__REWRITE_DB_PROOF_CONS__H
#define CVC4__THEORY__REWRITE_DB_PROOF_CONS__H

#include <map>

#include "expr/match_trie.h"
#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "theory/evaluator.h"
#include "theory/rewrite_db.h"
#include "theory/rewrite_db_term_process.h"
#include "theory/rewrite_rcons.h"

namespace cvc5 {
namespace theory {

class RewriteDbProofCons
{
 public:
  RewriteDbProofCons(RewriteDb* db, ProofNodeManager* pnm);
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
  Evaluator d_eval;
  class ProvenInfo
  {
   public:
    ProvenInfo() : d_id(rewriter::DslPfRule::FAIL), d_failMaxDepth(0) {}
    /** The identifier of the proof rule */
    rewriter::DslPfRule d_id;
    /** The substitution */
    std::vector<Node> d_vars;
    std::vector<Node> d_subs;
    /** the maximum depth tried for rules that have failed */
    uint32_t d_failMaxDepth;
    /** The inflection conditions */
    std::vector<Node> d_iconds;
  };
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
  /** prove internal */
  rewriter::DslPfRule proveInternal(Node eqi);
  /** prove internal base eqi * { vars -> subs } */
  bool proveInternalBase(Node eqi, rewriter::DslPfRule& id);
  /** ensure proof for proven fact exists in cdp */
  bool ensureProofInternal(CDProof* cdp, Node eqi);
  /** ensure proof skeleton */
  void ensureProofSkeletonInternal(CDProof* cdp, Node a, Node b);
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
  /**
   * Inflect match, if possible, return a modified form of n that matches s
   * with subs.
   *
   * In particular, for return term ret, we have:
   * ret * isubs.first = n
   * ret * isubs.second = s
   */
  Node inflectMatch(Node n,
                    Node s,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    std::unordered_map<Node, std::pair<Node, Node>>& isubs);
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__THEORY__REWRITE_DB_PROOF_CONS__H */
