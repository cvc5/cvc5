/*********************                                                        */
/*! \file rewrite_db_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database proof generator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__REWRITE_DB_PROOF_GENERATOR__H
#define CVC4__THEORY__REWRITE_DB_PROOF_GENERATOR__H

#include <map>

#include "expr/match_trie.h"
#include "expr/node.h"
#include "expr/proof_generator.h"
#include "theory/rewrite_db.h"
#include "theory/evaluator.h"

namespace CVC4 {
namespace theory {


  
class RewriteDbProofCons : public ProofGenerator
{ 
 public:
  RewriteDbProofCons(RewriteDb& db);
  /** Prove? */
  bool prove(Node a, Node b, unsigned recDepth);
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;
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
  /** reference to rewrite database */
  RewriteDb& d_db;
  /** the evaluator utility */
  Evaluator d_eval;
  /** cache for exists rule */
  std::unordered_map<Node, unsigned, NodeHashFunction> d_pcache;
  /** the maximum depth tried for rules that have failed */
  std::unordered_map<Node, unsigned, NodeHashFunction> d_pcacheFailMaxDepth;
  /** common constants */
  Node d_true;
  Node d_false;
  /** current recursion limit */
  unsigned d_currRecLimit;
  /** prove internal */
  unsigned proveInternal(Node eqi);
  /** prove internal base */
  unsigned proveInternalBase(Node eqi);
  /**
   * A notification that s is equal to n * { vars -> subs }. This function
   * should return false if we do not wish to be notified of further matches.
   */
  bool notifyMatch(Node s,
              Node n,
              std::vector<Node>& vars,
              std::vector<Node>& subs);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__REWRITE_DB_PROOF_GENERATOR__H */
