/*********************                                                        */
/*! \file sygus_unif_io.h
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
                  Node f,
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
  /** set of refinmente lemmas */
  std::vector<Node> d_refLemmas;
  /** initialize construct solution */
  void initializeConstructSol() override;
  /** construct solution */
  Node constructSol(Node e, NodeRole nrole, int ind) override;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H */
