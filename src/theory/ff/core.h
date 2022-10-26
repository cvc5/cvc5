/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields UNSAT trace construction
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__INC_TRACE_H
#define CVC5__THEORY__FF__INC_TRACE_H

#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ring.H>

#include <functional>
#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

// An incremental dependency graph for CoCoA polynomials in Groebner basis
// computation.
class IncrementalTracer
{
 public:
  // Empty graph
  IncrementalTracer();
  // Hook up to CoCoA handlers.
  void setFunctionPointers();
  // Add an input to the graph
  void addInput(const CoCoA::RingElem& i);
  // Get the index of inputs responsible for this element.
  std::vector<size_t> trace(const CoCoA::RingElem& i) const;
  // Enter a new context
  void push();
  // Remove last context. Resets graph to its state before that context.
  void pop();

 private:
  void sPoly(CoCoA::ConstRefRingElem p,
             CoCoA::ConstRefRingElem q,
             CoCoA::ConstRefRingElem s);
  void reductionStart(CoCoA::ConstRefRingElem p);
  void reductionStep(CoCoA::ConstRefRingElem q);
  void reductionEnd(CoCoA::ConstRefRingElem r);

  void addItem(const std::string&& item);
  void addDep(const std::string& parent, const std::string& child);

  std::unordered_map<std::string, std::vector<std::string>> d_parents{};
  std::unordered_map<std::string, std::unordered_set<std::string>> d_children{};
  std::unordered_map<std::string, size_t> d_inputNumbers{};
  std::vector<std::vector<std::string>> d_inputs{};
  size_t d_nInputs{};
  std::vector<std::string> d_reductionSeq{};

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

#endif /* CVC5__THEORY__FF__INC_TRACE_H */

#endif /* CVC5_USE_COCOA */
