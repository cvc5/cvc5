/*********************                                                        */
/*! \file candidate_rewrite_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief candidate_rewrite_database
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H
#define CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>
#include "theory/quantifiers/candidate_rewrite_filter.h"
#include "theory/quantifiers/expr_miner.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** CandidateRewriteDatabase
 *
 * This maintains the necessary data structures for generating a database
 * of candidate rewrite rules (see Reynolds et al "Rewrites for SMT Solvers
 * Using Syntax-Guided Enumeration" SMT 2018). The primary responsibilities
 * of this class are to perform the "equivalence checking" and "congruence
 * and matching filtering" in Figure 1. The equivalence checking is done
 * through a combination of the sygus sampler object owned by this class
 * and the calls made to copies of the SmtEngine in ::addTerm. The rewrite
 * rule filtering (based on congruence, matching, variable ordering) is also
 * managed by the sygus sampler object.
 */
class CandidateRewriteDatabase : public ExprMiner
{
 public:
  CandidateRewriteDatabase();
  ~CandidateRewriteDatabase() {}
  /**  Initialize this class */
  void initialize(const std::vector<Node>& var,
                  SygusSampler* ss = nullptr) override;
  /**  Initialize this class
   *
   * Serves the same purpose as the above function, but we will be using
   * sygus to enumerate terms and generate samples.
   *
   * qe : pointer to quantifiers engine. We use the sygus term database of this
   * quantifiers engine, and the extended rewriter of the corresponding term
   * database when computing candidate rewrites,
   * f : a term of some SyGuS datatype type whose values we will be
   * testing under the free variables in the grammar of f. This is the
   * "candidate variable" CegConjecture::d_candidates.
   */
  void initializeSygus(const std::vector<Node>& vars,
                       QuantifiersEngine* qe,
                       Node f,
                       SygusSampler* ss = nullptr);
  /** add term
   *
   * Notifies this class that the solution sol was enumerated. This may
   * cause a candidate-rewrite to be printed on the output stream out.
   * We return true if the term sol is distinct (up to equivalence) with
   * all previous terms added to this class. The argument rew_print is set to
   * true if this class printed a rewrite involving sol.
   *
   * If the flag rec is true, then we also recursively add all subterms of sol
   * to this class as well.
   */
  bool addTerm(Node sol, bool rec, std::ostream& out, bool& rew_print);
  bool addTerm(Node sol, bool rec, std::ostream& out);
  bool addTerm(Node sol, std::ostream& out) override;
  /** sets whether this class should output candidate rewrites it finds */
  void setSilent(bool flag);
  /** set the (extended) rewriter used by this class */
  void setExtendedRewriter(ExtendedRewriter* er);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** (required) pointer to the sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** an extended rewriter object */
  ExtendedRewriter* d_ext_rewrite;
  /** the function-to-synthesize we are testing (if sygus) */
  Node d_candidate;
  /** whether we are using sygus */
  bool d_using_sygus;
  /** candidate rewrite filter */
  CandidateRewriteFilter d_crewrite_filter;
  /** the cache for results of addTerm */
  std::unordered_map<Node, bool, NodeHashFunction> d_add_term_cache;
  /** if true, we silence the output of candidate rewrites */
  bool d_silent;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H */
