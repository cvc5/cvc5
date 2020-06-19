/*********************                                                        */
/*! \file candidate_rewrite_filter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements techniques for candidate rewrite rule filtering, which
 ** filters the output of --sygus-rr-synth. The classes in this file implement
 ** filtering based on congruence, variable ordering, and matching.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_FILTER_H
#define CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_FILTER_H

#include <map>
#include "expr/match_trie.h"
#include "theory/quantifiers/dynamic_rewrite.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** candidate rewrite filter
 *
 * This class is responsible for various filtering techniques for candidate
 * rewrite rules, including:
 * (1) filtering based on variable ordering,
 * (2) filtering based on congruence,
 * (3) filtering based on matching.
 * For details, see Reynolds et al "Rewrites for SMT Solvers using Syntax-Guided
 * Enumeration", SMT 2018.
 *
 * In the following, we assume that the registerRelevantPair method of this
 * class been called for some pairs of terms. For each such call to
 * registerRelevantPair( t, s ), we say that (t,s) and (s,t) are "relevant
 * pairs". A relevant pair ( t, s ) typically corresponds to a (candidate)
 * rewrite t = s.
 */
class CandidateRewriteFilter
{
 public:
  CandidateRewriteFilter();

  /** initialize
   *
   * Initializes this class, ss is the sygus sampler that this class is
   * filtering rewrite rule pairs for, and tds is a point to the sygus term
   * database utility class.
   *
   * If useSygusType is false, this means that the terms in filterPair and
   * registerRelevantPair calls should be interpreted as themselves. Otherwise,
   * if useSygusType is true, these terms should be interpreted as their
   * analog according to the deep embedding.
   */
  void initialize(SygusSampler* ss, TermDbSygus* tds, bool useSygusType);
  /** filter pair
   *
   * This method returns true if the pair (n, eq_n) should be filtered. If it
   * is not filtered, then the caller may choose to call
   * registerRelevantPair(n, eq_n) below, although it may not, say if it finds
   * another reason to discard the pair.
   *
   * If this method returns false, then for all previous relevant pairs
   * ( a, eq_a ), we have that n = eq_n is not an instance of a = eq_a
   * modulo symmetry of equality, nor is n = eq_n derivable from the set of
   * all previous relevant pairs. The latter is determined by the d_drewrite
   * utility. For example:
   * [1]  ( t+0, t ) and ( x+0, x )
   * will not both be relevant pairs of this function since t+0=t is
   * an instance of x+0=x.
   * [2]  ( s, t ) and ( s+0, t+0 )
   * will not both be relevant pairs of this function since s+0=t+0 is
   * derivable from s=t.
   * These two criteria may be combined, for example:
   * [3] ( t+0, s ) is not a relevant pair if both ( x+0, x+s ) and ( t+s, s )
   * are relevant pairs, since t+0 is an instance of x+0 where
   * { x |-> t }, and x+s { x |-> t } = s is derivable, via the third pair
   * above (t+s = s).
   */
  bool filterPair(Node n, Node eq_n);
  /** register relevant pair
   *
   * This should be called after filterPair( n, eq_n ) returns false.
   * This registers ( n, eq_n ) as a relevant pair with this class.
   */
  void registerRelevantPair(Node n, Node eq_n);

 private:
  /** pointer to the sygus sampler that this class is filtering rewrites for */
  SygusSampler* d_ss;
  /** pointer to the sygus term database, used if d_use_sygus_type is true */
  TermDbSygus* d_tds;
  /** whether we are registering sygus terms with this class */
  bool d_use_sygus_type;

  //----------------------------congruence filtering
  /** a (dummy) user context, used for d_drewrite */
  context::UserContext d_fake_context;
  /** dynamic rewriter class */
  std::unique_ptr<DynamicRewriter> d_drewrite;
  //----------------------------end congruence filtering

  //----------------------------match filtering
  /**
   * Stores all relevant pairs returned by this sampler (see registerTerm). In
   * detail, if (t,s) is a relevant pair, then t in d_pairs[s].
   */
  std::map<Node, std::unordered_set<Node, NodeHashFunction> > d_pairs;
  /**
   * For each (builtin) type, a match trie storing all terms in the domain of
   * d_pairs.
   *
   * Notice that we store d_drewrite->toInternal(t) instead of t, for each
   * term t, so that polymorphism is handled properly. In particular, this
   * prevents matches between terms select( x, y ) and select( z, y ) where
   * the type of x and z are different.
   */
  std::map<TypeNode, expr::MatchTrie> d_match_trie;
  /** Notify class */
  class CandidateRewriteFilterNotifyMatch : public expr::NotifyMatch
  {
    CandidateRewriteFilter& d_sse;

   public:
    CandidateRewriteFilterNotifyMatch(CandidateRewriteFilter& sse) : d_sse(sse)
    {
    }
    /** notify match */
    bool notify(Node n,
                Node s,
                std::vector<Node>& vars,
                std::vector<Node>& subs) override
    {
      return d_sse.notify(n, s, vars, subs);
    }
  };
  /** Notify object used for reporting matches from d_match_trie */
  CandidateRewriteFilterNotifyMatch d_ssenm;
  /**
   * Stores the current right hand side of a pair we are considering.
   *
   * In more detail, in registerTerm, we are interested in whether a pair (s,t)
   * is a relevant pair. We do this by:
   * (1) Setting the node d_curr_pair_rhs to t,
   * (2) Using d_match_trie, compute all terms s1...sn that match s.
   * For each si, where s = si * sigma for some substitution sigma, we check
   * whether t = ti * sigma for some previously relevant pair (si,ti), in
   * which case (s,t) is an instance of (si,ti).
   */
  Node d_curr_pair_rhs;
  /**
   * Called by the above class during d_match_trie.getMatches( s ), when we
   * find that si = s * sigma, where si is a term that is stored in
   * d_match_trie.
   *
   * This function returns false if ( s, d_curr_pair_rhs ) is an instance of
   * previously relevant pair.
   */
  bool notify(Node s, Node n, std::vector<Node>& vars, std::vector<Node>& subs);
  //----------------------------end match filtering
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_FILTER_H */
