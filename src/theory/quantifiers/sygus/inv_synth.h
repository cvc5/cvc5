/*********************                                                        */
/*! \file inv_synth.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for specialized approaches for invariant synthesis
 **/
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS__INV_SYNTH_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS__INV_SYNTH_H

#include <map>
#include <string>
#include <vector>

#include "expr/datatype.h"
#include "expr/node.h"
#include "expr/type.h"
#include "expr/type_node.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Synthesizes invariants
 *
 * The primary approach consists of successively strengthening and weakining
 * candidate invariants based on counterexamples produced during verification
 * that the invariant satisfies all conditions
 *
 * Synthesis is used for deriving "features", atomic expressions that are used
 * to separate "good", "bad", and "conditional" valuations to the state
 * variables in the transition system. Once points can be separated without
 * conflicts, an arbitrary CNF is built with the features, thus yielding the
 * invariant.
 *
 * Strengthening occurs when testing the candidate yields a "bad" or a
 * "conditional" valuation, while weakining when testing yields a "good"
 * point. "Good" points are those in which the invariant must always hold, "bad"
 * in which it must never hold, and "conditional" those in which the invariant
 * cannot hold then fail to hold (representing the invariant not being respected
 * by the transition relation). Good and bad points are independent of the
 * candidate being derived, while conditional points are good points which yield
 * bad points for an specific candidate.
 *
 * This appoarch is inspired by Padhi et al. PLDI 2016
 */
class InvSynth
{
 public:
  InvSynth(QuantifiersEngine* qe)
      : d_qe(qe)
  {
  }
  ~InvSynth() {}

  /** initialize this class */
  void initialize(Node n);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;

}; /* class InvSynth */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
