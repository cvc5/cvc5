/*********************                                                        */
/*! \file theory_rewriterules.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewrite Engine classes
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H
#define __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H

#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "theory/valuation.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "context/context_mm.h"
#include "theory/rewriterules/rr_inst_match_impl.h"
#include "theory/rewriterules/rr_trigger.h"
#include "theory/rewriterules/rr_inst_match.h"
#include "util/statistics_registry.h"
#include "theory/rewriterules/theory_rewriterules_preprocess.h"

namespace CVC4 {
namespace theory {
namespace rewriterules {
using namespace CVC4::theory::rrinst;
typedef CVC4::theory::rrinst::Trigger Trigger;

typedef std::hash_map<TNode, TNode, TNodeHashFunction> TCache;

  enum Answer {ATRUE, AFALSE, ADONTKNOW};

  class TheoryRewriteRules; /** forward */

  class RewriteRule{
  public:
    // constant
    const size_t id; //for debugging
    const bool d_split;
    mutable Trigger trigger;
    std::vector<Node> guards;
    mutable std::vector<Node> to_remove; /** terms to remove */
    const Node body;
    const TNode new_terms; /** new terms included in the body */
    std::vector<Node> free_vars; /* free variable in the rule */
    std::vector<Node> inst_vars; /* corresponding vars in the triggers */
    /* After instantiating the body new match can appear (TNode
       because is a subterm of a body on the assicaited rewrite
       rule) */
    typedef context::CDList< std::pair<TNode,RewriteRule* > > BodyMatch;
    mutable BodyMatch body_match;
    mutable ApplyMatcher * trigger_for_body_match; // used because we can be matching
                                    // trigger when we need new match.
                                    // So currently we use another
                                    // trigger for that.

    //context dependent
    typedef InstMatchTrie2<true> CacheNode;
    mutable CacheNode d_cache;

    const bool directrr;

    RewriteRule(TheoryRewriteRules & re,
                Trigger & tr, ApplyMatcher * tr2,
                std::vector<Node> & g, Node b, TNode nt,
                std::vector<Node> & fv,std::vector<Node> & iv,
                std::vector<Node> & to_r, bool drr);
    RewriteRule(const RewriteRule & r) CVC4_UNUSED;
    RewriteRule& operator=(const RewriteRule &) CVC4_UNUSED;
    ~RewriteRule();

    bool noGuard()const throw () { return guards.size() == 0; };
    bool inCache(TheoryRewriteRules & re, rrinst::InstMatch & im)const;

    void toStream(std::ostream& out) const;

    /* statistics */
    mutable size_t nb_matched;
    mutable size_t nb_applied;
    mutable size_t nb_propagated;

  };

  class RuleInst{
  public:
    /** The rule has at least one guard */
    const RewriteRule* rule;

    /** the substitution */
    std::vector<Node> subst;

    /** the term matched (not null if mono-pattern and direct-rr) */
    Node d_matched;

    /** Rule an instantiation with the given match */
    RuleInst(TheoryRewriteRules & re, const RewriteRule* r,
             std::vector<Node> & inst_subst,
             Node matched);
    RuleInst():rule(NULL){} // Dumb

    Node substNode(const TheoryRewriteRules & re, TNode r, TCache cache) const;
    size_t findGuard(TheoryRewriteRules & re, size_t start)const;

    void toStream(std::ostream& out) const;

    bool alreadyRewritten(TheoryRewriteRules & re) const;
  };

/** A pair? */
  class Guarded {
  public:
    /** The backtracking is done somewhere else */
    const size_t d_guard; /* the id of the guard */

    /** The shared instantiation data */
    const RuleInst* inst;

    void nextGuard(TheoryRewriteRules & re)const;

    /** start indicate the first guard which is not true */
    Guarded(const RuleInst* ri, const size_t start);
    Guarded(const Guarded & g);
    /** Should be ssigned by a good garded after */
    Guarded();

    ~Guarded(){};
    void destroy(){};
  };

template<class T>
class CleanUpPointer{
public:
  inline void operator()(T** e){
    delete(*e);
  };
};

class TheoryRewriteRules : public Theory {
private:

  KEEP_STATISTIC(TimerStat, d_theoryTime, "theory::rewriterules::theoryTime");

  /** list of all rewrite rules */
  /* std::vector< Node > d_rules; */
  // typedef std::vector< std::pair<Node, Trigger > > Rules;
  typedef context::CDList< RewriteRule *,
                           CleanUpPointer<RewriteRule >,
                           std::allocator< RewriteRule * > > Rules;
  Rules d_rules;
  typedef context::CDList< RuleInst *,
                           CleanUpPointer<RuleInst>,
                           std::allocator< RuleInst * > > RuleInsts;
  RuleInsts d_ruleinsts;

  /** The GList* will lead too memory leaks since that doesn't use
      CDChunckList */
  typedef context::CDList< Guarded > GList;
  typedef context::CDHashMap<Node, GList *, NodeHashFunction> GuardedMap;
  GuardedMap d_guardeds;

  /* In order to not monopolize, the system slow down himself: If a
     guard stored in d_guardeds become true or false, it waits
     checkSlowdown(=10) checks before checking again if some guard take a
     value. At FULL_EFFORT regardless of d_checkLevel it check the
     guards
   */
  context::CDO<size_t> d_checkLevel;

  /** explanation */
  typedef context::CDHashMap<Node, RuleInst , NodeHashFunction> ExplanationMap;
  ExplanationMap d_explanations;

  /** new instantiation must be cleared at each conflict used only
      inside check */
  typedef std::vector< RuleInst* > QRuleInsts;
  QRuleInsts d_ruleinsts_to_add;
  bool d_ppAssert_on; //Indicate if a ppAssert have been done

 public:
  /** true and false for predicate */
  Node d_true;
  Node d_false;

  /** Constructs a new instance of TheoryRewriteRules
      w.r.t. the provided context.*/
  TheoryRewriteRules(context::Context* c,
                     context::UserContext* u,
                     OutputChannel& out,
                     Valuation valuation,
                     const LogicInfo& logicInfo);

  /** Usual function for theories */
  void check(Theory::Effort e);
  Node explain(TNode n);
  void collectModelInfo( TheoryModel* m, bool fullModel );
  void notifyEq(TNode lhs, TNode rhs);
  std::string identify() const {
    return "THEORY_REWRITERULES";
  }

  Theory::PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  bool ppDontRewriteSubterm(TNode atom){ return true; }


 private:
  void registerQuantifier( Node n );

 public:
  /* TODO modify when notification will be available */
  void notification( Node n, bool b);

  Trigger createTrigger( TNode n, std::vector<Node> & pattern );

  /** return if the guard (already substituted) is known true or false
      or unknown. In the last case it add the Guarded(rid,gid) to the watch
      list of this guard */
  Answer addWatchIfDontKnow(Node g, const RuleInst* r, const size_t gid);

  /** An instantiation of a rule is fired (all guards true) we
      propagate the body. That can be done by theory propagation if
      possible or by lemmas.
   */
  void propagateRule(const RuleInst * r, TCache cache);

  /** Auxiliary functions */
private:
  /** A guard is verify, notify the Guarded */
  void notification(GList * const lpropa, bool b);
  /* If two guards becomes equals we should notify if one of them is
     already true */
  bool notifyIfKnown(const GList * const ltested, GList * const lpropa);

  void substGuards(const RuleInst * inst,
                   TCache cache,
                   NodeBuilder<> & conjunction);

  void addRewriteRule(const Node r);
  void computeMatchBody ( const RewriteRule * r, size_t start = 0);
  void addMatchRuleTrigger(const RewriteRule* r,
                           rrinst::InstMatch & im, bool delay = true);

  Node normalizeConjunction(NodeBuilder<> & conjunction);

  /* rewrite pattern */
  typedef std::hash_map< Node, rewriter::RRPpRewrite*, NodeHashFunction > RegisterRRPpRewrite;
  RegisterRRPpRewrite d_registeredRRPpRewrite;

  bool addRewritePattern(TNode pattern, TNode body,
                         rewriter::Subst & pvars,
                         rewriter::Subst & vars);

  //create inst variable
  std::vector<Node> createInstVariable( Node r, std::vector<Node> & vars );

    /** statistics class */
  class Statistics {
  public:
    IntStat d_num_rewriterules;
    IntStat d_check;
    IntStat d_full_check;
    IntStat d_poll;
    IntStat d_match_found;
    IntStat d_cache_hit;
    IntStat d_cache_miss;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;

};/* class TheoryRewriteRules */

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__THEORY_REWRITERULES_H */
