/*********************                                                        */
/*! \file candidate_rewrite_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief candidate_rewrite_database
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H
#define __CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>
#include "theory/quantifiers/candidate_rewrite_filter.h"
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
class CandidateRewriteDatabase
{
 public:
  CandidateRewriteDatabase();
  ~CandidateRewriteDatabase() {}
  /**  Initialize this class
   *
   * er : pointer to the extended rewriter (if any) we are using to compute
   * candidate rewrites,
   * tn : the return type of terms we will be testing with this class,
   * vars : the variables we are testing substitutions for,
   * nsamples : number of sample points this class will test,
   * unique_type_ids : if this is set to true, then each variable is treated
   * as unique. This affects whether or not a rewrite rule is considered
   * redundant or not. For example the rewrite f(y)=y is redundant if
   * f(x)=x has also been printed as a rewrite and x and y have the same type
   * id (see SygusSampler for details). On the other hand, when a candidate
   * rewrite database is initialized with sygus below, the type ids of the
   * (sygus formal argument list) variables are always computed and used.
   */
  void initialize(ExtendedRewriter* er,
                  TypeNode tn,
                  std::vector<Node>& vars,
                  unsigned nsamples,
                  bool unique_type_ids = false);
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
   * "candidate variable" CegConjecture::d_candidates,
   * nsamples : number of sample points this class will test,
   * useSygusType : whether we will register terms with this sampler that have
   * the same type as f. If this flag is false, then we will be registering
   * terms of the analog of the type of f, that is, the builtin type that
   * f's type encodes in the deep embedding.
   *
   * These arguments are used to initialize the sygus sampler class.
   */
  void initializeSygus(QuantifiersEngine* qe,
                       Node f,
                       unsigned nsamples,
                       bool useSygusType);
  /** add term
   *
   * Notifies this class that the solution sol was enumerated. This may
   * cause a candidate-rewrite to be printed on the output stream out.
   * We return true if the term sol is distinct (up to equivalence) with
   * all previous terms added to this class. The argument rew_print is set to
   * true if this class printed a rewrite.
   */
  bool addTerm(Node sol, std::ostream& out, bool& rew_print);
  bool addTerm(Node sol, std::ostream& out);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** pointer to the sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** pointer to the extended rewriter object we are using */
  ExtendedRewriter* d_ext_rewrite;
  /** the (sygus or builtin) type of terms we are testing */
  TypeNode d_type;
  /** the function-to-synthesize we are testing (if sygus) */
  Node d_candidate;
  /** whether we are using sygus */
  bool d_using_sygus;
  /** sygus sampler objects for each program variable
   *
   * This is used for the sygusRewSynth() option to synthesize new candidate
   * rewrite rules.
   */
  SygusSampler d_sampler;
  /** candidate rewrite filter */
  CandidateRewriteFilter d_crewrite_filter;
  /**
   * Cache of skolems for each free variable that appears in a synthesis check
   * (for --sygus-rr-synth-check).
   */
  std::map<Node, Node> d_fv_to_skolem;
};

/**
 * This class generates and stores candidate rewrite databases for multiple
 * types as needed.
 */
class CandidateRewriteDatabaseGen
{
 public:
  /** constructor
   *
   * vars : the variables we are testing substitutions for, for all types,
   * nsamples : number of sample points this class will test for all types.
   */
  CandidateRewriteDatabaseGen(std::vector<Node>& vars, unsigned nsamples);
  /** add term
   *
   * This registers term n with this class. We generate the candidate rewrite
   * database of the appropriate type (if not allocated already), and register
   * n with this database. This may result in "candidate-rewrite" being
   * printed on the output stream out.
   */
  bool addTerm(Node n, std::ostream& out);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** the variables */
  std::vector<Node> d_vars;
  /** the number of samples */
  unsigned d_nsamples;
  /** candidate rewrite databases for each type */
  std::map<TypeNode, CandidateRewriteDatabase> d_cdbs;
  /** an extended rewriter object */
  ExtendedRewriter d_ext_rewrite;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H */
