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

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Sygus unification Refinement Lemmas utility
 *
 * This class implement synthesis-by-unification, where the specification is a
 * set of refinement lemmas. With respect to SygusUnif, it's main interface
 * function is addExample, which adds a refinement lemma to the specification.
 */
class SygusUnifRl : public SygusUnif
{
 public:
  SygusUnifRl();
  ~SygusUnifRl();

  /** initialize */
  void initialize(QuantifiersEngine* qe,
                  const std::vector<Node>& funs,
                  std::vector<Node>& enums,
                  std::vector<Node>& lemmas) override;
  /** Notify enumeration */
  void notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas) override;
  /** add refinement lemma
   *
   * This adds a lemma to the specification for f.
   */
  void addRefLemma(Node lemma);

 protected:
  /** true and false nodes */
  Node d_true, d_false;
  /** current collecton of refinement lemmas */
  Node d_rlemmas;
  /** previous collecton of refinement lemmas */
  Node d_prev_rlemmas;
  /** whether there are refinement lemmas to satisfy when building solutions */
  bool d_hasRLemmas;
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
  /**
   * Returns a term covering all data points in the current branch, on null if
   * none can be found among the currently enumerated values for the respective
   * enumerator
   */
  Node canCloseBranch(Node e);

  /** construct solution */
  Node constructSol(Node f, Node e, NodeRole nrole, int ind) override;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H */
