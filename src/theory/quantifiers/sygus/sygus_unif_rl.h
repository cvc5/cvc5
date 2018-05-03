/*********************                                                        */
/*! \file sygus_unif_rl.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_unif_rl
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H

#include <map>
#include "theory/quantifiers/sygus/sygus_unif.h"

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

using BoolNodePair = std::pair<bool, Node>;
using BoolNodePairHashFunction =
    PairHashFunction<bool, Node, BoolHashFunction, NodeHashFunction>;
using BoolNodePairMap =
    std::unordered_map<BoolNodePair, Node, BoolNodePairHashFunction>;

class CegConjecture;

/** Sygus unification Refinement Lemmas utility
 *
 * This class implement synthesis-by-unification, where the specification is a
 * set of refinement lemmas. With respect to SygusUnif, it's main interface
 * function is addExample, which adds a refinement lemma to the specification.
 */
class SygusUnifRl : public SygusUnif
{
 public:
  SygusUnifRl(CegConjecture* p);
  ~SygusUnifRl();

  /** initialize */
  void initialize(QuantifiersEngine* qe,
                  const std::vector<Node>& funs,
                  std::vector<Node>& enums,
                  std::vector<Node>& lemmas) override;
  /** Notify enumeration */
  void notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas) override;
  /** Construct solution */
  bool constructSolution(std::vector<Node>& sols) override;
  Node constructSol(Node f, Node e, NodeRole nrole, int ind) override;
  /** add refinement lemma
   *
   * This adds a lemma to the specification for f.
   */
  Node addRefLemma(Node lemma);
  /**
   * whether f is being synthesized with unification strategies. This can be
   * checked through wehether f has conditional or point enumerators (we use the
   * former)
    */
  bool usingUnif(Node f);

 protected:
  /** reference to the parent conjecture */
  CegConjecture* d_parent;
  /* Functions-to-synthesize (a.k.a. candidates) with unification strategies */
  std::unordered_set<Node, NodeHashFunction> d_unif_candidates;
  /* Maps unif candidates to their conditonal enumerators */
  std::map<Node, Node> d_cand_to_cond_enum;
  /**
   * This class stores information regarding an enumerator, including: a
   * database
   * of values that have been enumerated for this enumerator.
   */
  class EnumCache
  {
   public:
    EnumCache() {}
    ~EnumCache() {}
    /** Values that have been enumerated for this enumerator */
    std::vector<Node> d_enum_vals;
  };
  /** maps enumerators to the information above */
  std::map<Node, EnumCache> d_ecache;

  /** collects data from refinement lemmas to drive solution construction
   *
   * In particular it rebuilds d_app_to_pt whenever d_prev_rlemmas is different
   * from d_rlemmas, in which case we may have added or removed data points
   */
  void initializeConstructSol() override;
  /** initialize construction solution for function-to-synthesize f */
  void initializeConstructSolFor(Node f) override;
  /*
    --------------------------------------------------------------
        Purification
    --------------------------------------------------------------
  */
  /* Maps unif candidates to their point enumerators */
  std::map<Node, std::vector<Node>> d_cand_to_pt_enum;
  /**
   * maps applications of the function-to-synthesize to their tuple of arguments
   * (which constitute a "data point") */
  std::map<Node, std::vector<Node>> d_app_to_pt;
  /** Maps applications of unif functions-to-synthesize to purified symbols*/
  std::map<Node, Node> d_app_to_purified;
  /** Maps unif functions-to-synthesize to counters of purified symbols */
  std::map<Node, unsigned> d_purified_count;
  /**
   * This is called on the refinement lemma and will rewrite applications of
   * functions-to-synthesize to their respective purified form, i.e. such that
   * all unification functions are applied over concrete values. Moreover
   * unification functions are also rewritten such that every different tuple of
   * arguments has a fresh function symbol applied to it.
   *
   * Non-unification functions are also equated to their model values when they
   * occur as arguments of unification functions.
   *
   * A vector of guards with the (negated) equalities between the original
   * arguments and their model values is populated accordingly.
   *
   * When the traversal encounters an application of a unification
   * function-to-synthesize it will proceed to ensure that the arguments of that
   * function application are constants (the ensureConst becomes "true"). If an
   * applicatin of a non-unif function-to-synthesize is reached, the requirement
   * is lifted (the ensureConst becomes "false"). This avoides introducing
   * spurious equalities in model_guards.
   *
   * For example if "f" is being synthesized with a unification strategy and "g"
   * is not then the application
   *   f(g(f(g(0))))=1
   * would be purified into
   *   g(0) = c1 ^ g(f1(c1)) = c3 => f2(c3)
   *
   * Similarly
   *   f(+(0,f(g(0))))
   * would be purified into
   *   g(0) = c1 ^ f1(c1) = c2 => f2(+(0,c2))
   *
   * This function also populates the maps for point enumerators
   */
  Node purifyLemma(Node n,
                   bool ensureConst,
                   std::vector<Node>& model_guards,
                   BoolNodePairMap& cache);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H */
