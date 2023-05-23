/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields UNSAT trace construction
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__CORE_H
#define CVC5__THEORY__FF__CORE_H

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ring.H>

#include <functional>
#include <unordered_map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * A non-incremental dependency graph for CoCoA polynomials in Groebner basis
 * computation.
 *
 * We represent polynomials as their strings.
 */
class Tracer
{
 public:
  /**
   * Set up tracing for these inputs.
   * Creating it connects to the CoCoA callbacks.
   */
  Tracer(const std::vector<CoCoA::RingElem>& inputs);

  /**
   * Get the index of inputs responsible for this element.
   */
  std::vector<size_t> trace(const CoCoA::RingElem& i) const;

  /** CoCoA callback management */

  /**
   * Hook up to CoCoA callbacks. Don't move the object after calling this. Must be called before CoCoA is used.
   */
  void setFunctionPointers();

  /**
   * Unhook from CoCoA callbacks. Should be called after you're done tracing.
   */
  void unsetFunctionPointers();

 private:


  /**
   * Call this when s = spoly(p, q);
   */
  void sPoly(CoCoA::ConstRefRingElem p,
             CoCoA::ConstRefRingElem q,
             CoCoA::ConstRefRingElem s);
  /**
   * Call this when we start reducing p.
   */
  void reductionStart(CoCoA::ConstRefRingElem p);
  /**
   * Call this when there is a reduction on q.
   */
  void reductionStep(CoCoA::ConstRefRingElem q);
  /**
   * Call this when we finish reducing with r.
   */
  void reductionEnd(CoCoA::ConstRefRingElem r);

  void addItem(const std::string&& item);
  void addDep(const std::string& parent, const std::string& child);

  /**
   * (key, vals) where key is in the ideal if vals are.
   */
  std::unordered_map<std::string, std::vector<std::string>> d_parents{};
  /**
   * For each poly string, its index in the input sequence.
   */
  std::unordered_map<std::string, size_t> d_inputNumbers;

  std::vector<std::string> d_reductionSeq{};

  /**
   * Handles to sPoly reductionStart, reductionStep, and reductionEnd that we
   * give to CoCoA.
   */
  std::function<void(CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem)>
      d_sPoly{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStart{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStep{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionEnd{};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__CORE_H */

#endif /* CVC5_USE_COCOA */
