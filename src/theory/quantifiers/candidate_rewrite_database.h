/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * candidate_rewrite_database
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H
#define CVC5__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H

#include <vector>

#include "options/options.h"
#include "theory/quantifiers/candidate_rewrite_filter.h"
#include "theory/quantifiers/expr_miner.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** CandidateRewriteDatabase
 *
 * This maintains the necessary data structures for generating a database
 * of candidate rewrite rules (see Noetzli et al "Syntax-Guided Rewrite Rule
 * Enumeration for SMT Solvers" SAT 2019). The primary responsibilities
 * of this class are to perform the "equivalence checking" and "congruence
 * and matching filtering" in Figure 1. The equivalence checking is done
 * through a combination of the sygus sampler object owned by this class
 * and the calls made to copies of the SolverEngine in ::addTerm. The rewrite
 * rule filtering (based on congruence, matching, variable ordering) is also
 * managed by the sygus sampler object.
 */
class CandidateRewriteDatabase : public ExprMiner
{
 public:
  /**
   * Constructor
   * @param env Reference to the environment
   * @param doCheck Whether to check rewrite rules using subsolvers.
   * @param rewAccel Whether to construct symmetry breaking lemmas based on
   * discovered rewrites (see option sygusRewSynthAccel()).
   * @param filterPairs Whether to filter rewrite pairs using filtering
   * techniques from the SAT 2019 paper above.
   * @param rec Whether we are recursively finding rules for all subterms
   * added to this class
   */
  CandidateRewriteDatabase(Env& env,
                           bool doCheck,
                           bool rewAccel = false,
                           bool filterPairs = true,
                           bool rec = false);
  ~CandidateRewriteDatabase() {}
  /**  Initialize this class */
  void initialize(const std::vector<Node>& var, SygusSampler* ss) override;
  /**  Initialize this class
   *
   * Serves the same purpose as the above function, but we will be using
   * sygus to enumerate terms and generate samples.
   *
   * tds : pointer to sygus term database. We use the extended rewriter of this
   * database when computing candidate rewrites,
   * f : a term of some SyGuS datatype type whose values we will be
   * testing under the free variables in the grammar of f. This is the
   * "candidate variable" CegConjecture::d_candidates.
   */
  void initializeSygus(const std::vector<Node>& vars,
                       TermDbSygus* tds,
                       Node f,
                       SygusSampler* ss);
  /** add term
   *
   * Notifies this class that the solution sol was enumerated. This may
   * cause a candidate-rewrite to be printed on the output stream out.
   *
   * @param sol The term to add to this class.
   * @param rewrites The set of rewrite rules discovered on this call.
   * @return A previous term eq_sol added to this class, such that sol is
   * equivalent to eq_sol based on the criteria used by this class. We return
   * only terms that are verified to be equivalent to sol.
   */
  Node addOrGetTerm(Node sol, std::vector<Node>& rewrites);
  /**
   * Same as above, returns true if the return value of addTerm was equal to
   * sol, in other words, sol was a new unique term. This assumes false for
   * the argument rec.
   */
  bool addTerm(Node sol, std::vector<Node>& rewrites) override;
  /** Enable the (extended) rewriter for this class */
  void enableExtendedRewriter();
  /** Was the given rewrite verified? */
  bool wasVerified(const Node& rewrite) const;

 private:
  /** (required) pointer to the sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** Whether we use the extended rewriter */
  bool d_useExtRewriter;
  /** the function-to-synthesize we are testing (if sygus) */
  Node d_candidate;
  /** whether we are checking equivalence using subsolver */
  bool d_doCheck;
  /**
   * If true, we use acceleration for symmetry breaking rewrites (see option
   * sygusRewSynthAccel()).
   */
  bool d_rewAccel;
  /** if true, we silence the output of candidate rewrites */
  bool d_silent;
  /** if true, we filter pairs of terms to check equivalence */
  bool d_filterPairs;
  /** whether we are using sygus */
  bool d_using_sygus;
  /** Whether we check rewrite rules for all subterms added to this class */
  bool d_rec;
  /** candidate rewrite filter */
  CandidateRewriteFilter d_crewrite_filter;
  /** the cache for results of addTerm */
  std::unordered_map<Node, Node> d_add_term_cache;
  /** The options for subsolver calls */
  Options d_subOptions;
  /** The set of rewrites that succeeded verification */
  std::unordered_set<Node> d_verified;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H */
