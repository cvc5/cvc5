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
  void addRefLemma(Node lemma);
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
  /* Maps unif candidates to their point enumerators */
  std::map<Node, std::vector<Node>> d_cand_to_pt_enum;
  /** true and false nodes */
  Node d_true, d_false;
  /** current collecton of refinement lemmas */
  Node d_rlemmas;
  /** previous collecton of refinement lemmas */
  Node d_prev_rlemmas;
  /**
   * maps applications of the function-to-synthesize to their tuple of arguments
   * (which constitute a "data point") */
  std::map<Node, std::vector<Node>> d_app_to_pt;
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

  /** Traverses n and populates d_app_to_pt */
  void collectPoints(Node n);

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

  /**
   * Maps applications of functions-to-synthesize to the respective purified
   * form of the function-to-synthesized. For example if "f" is being
   * synthesized with a unification strategy then applications such as
   *  f(c1,c2), f(c3,c4)
   * would be mapped into the symbols "f1" and "f2".
   */
  std::map<Node, Node> d_app_to_purified;
  /* Maps a function-to-synthesize to its counter of purified symbols */
  std::map<Node, unsigned> d_purified_count;
  /**
   * This is called on the refinement lemma and will replace the arguments of
   * the
   * function-to-synthesize by their model values (constants).
   *
   * When the traversal hits a function application of the
   * function-to-synthesize
   * it will proceed to ensure that the arguments of that function application
   * are constants (the ensureConst becomes "true"). It populates a vector of
   * guards with the (negated) equalities between the original arguments and
   * their model values.
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
