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
   * qe : pointer to quantifiers engine,
   * tn : the return type of terms we will be testing with this class,
   * vars : the variables we are testing substitutions for,
   * nsamples : number of sample points this class will test.
   */
  void initialize(QuantifiersEngine* qe,
                  TypeNode tn,
                  std::vector<Node>& vars,
                  unsigned nsamples);
  /**  Initialize this class
   *
   * Serves the same purpose as the above function, but we will be using
   * sygus to enumerate terms and generate samples.
   * 
   * qe : pointer to quantifiers engine,
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
   */
  bool addTerm(Node sol, std::ostream& out);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
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
  SygusSamplerExt d_sampler;
  /** dynamic rewriter class */
  std::unique_ptr<DynamicRewriter> d_drewrite;
  /**
   * Cache of skolems for each free variable that appears in a synthesis check
   * (for --sygus-rr-synth-check).
   */
  std::map<Node, Node> d_fv_to_skolem;
  /** initalize internal, called by initialize methods above */
  void initializeInternal(QuantifiersEngine* qe);
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
    * qe : pointer to quantifiers engine,
    * vars : the variables we are testing substitutions for, for all types,
    * nsamples : number of sample points this class will test for all types.
    */
   CandidateRewriteDatabaseGen(QuantifiersEngine* qe,
                   std::vector<Node>& vars,
                   unsigned nsamples);
   /** add term 
    * 
    * This registers term n with this class. We generate the candidate rewrite
    * database of the appropriate type (if not allocated already), and register
    * n with this database. This may result in "candidate-rewrite" being
    * printed on the output stream out.
    */
   void addTerm( Node n, std::ostream& out );
 private:
   /** reference to quantifier engine */
   QuantifiersEngine* d_qe;
   /** the variables */
   std::vector< Node > d_vars;
   /** the number of samples */
   unsigned d_nsamples;
   /** candidate rewrite databases for each type */
   std::map<TypeNode,CandidateRewriteDatabase> d_cdbs;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_DATABASE_H */
