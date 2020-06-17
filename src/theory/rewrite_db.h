/*********************                                                        */
/*! \file rewrite_db.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__REWRITE_DB__H
#define CVC4__THEORY__REWRITE_DB__H

#include <map>

#include "expr/match_trie.h"
#include "expr/node.h"
#include "expr/term_canonize.h"
#include "theory/rewrite_db_term_process.h"
#include "theory/rewrite_proof_rule.h"

namespace CVC4 {
namespace theory {

/**
 * A database of conditional rewrite rules.
 */
class RewriteDb
{
 public:
  RewriteDb();
  ~RewriteDb() {}
  /** Add rule, return its identifier */
  unsigned addRule(Node a, Node b, Node cond, const std::string& name);
  /** get matches */
  void getMatches(Node a, Node b, expr::NotifyMatch* ntm);

 private:
  /** common constants */
  Node d_true;
  Node d_false;
  /** the term process utility */
  RewriteDbTermProcess d_rdtp;
  /** the term canonization utility */
  expr::TermCanonize d_canon;
  /** The match trie */
  expr::MatchTrie d_mt;
  /** map ids to rewrite db rule information */
  std::map<unsigned, RewritePfRule> d_rewDbRule;
  /** currently allocating id */
  unsigned d_idCounter;
};

// TrustNode prove(Node a, Node b);

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__REWRITE_DB__H */
