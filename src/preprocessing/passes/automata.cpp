/******************************************************************************
 * Top contributors (to current version):
 *
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Automata preprocessing pass.
 *
 */

#include "preprocessing/passes/automata.h"

#include <cmath>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace {

}
/* -------------------------------------------------------------------------- */

void printDfa(const std::map<int, std::map<int, std::pair<int, int>>>& dfa)
{
  for (const auto& [state, transitions] : dfa)
  {
    std::cout << state << std::endl;
    for (const auto& [next_state, acc] : transitions)
    {
      std::cout << next_state << "," << acc << " ";
    }
    std::cout << std::endl;
  }
}

void buildDfa(std::map<int, std::map<int, std::pair<int, int>>>& dfa)
{
  std::pair<int, int> words[] = {{0, 0}, {0, 1}, {1, 0}, {1, 1}};
  int a1 = 1, a2 = 2, c = 1;
  dfa[c] = {};
  int k;
  for (auto& [x, y] : words)
  {
    k = c - a1 * x - a2 * y;
    if (k % 2 == 0)
    {
      dfa.insert({k / 2, {}});
    }
  }
}

Automata::Automata(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "automata")
{
}

PreprocessingPassResult Automata::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::cout << "Applying internal for automata preprocessing" << std::endl;
  AlwaysAssert(!options().base.incrementalSolving);

  /* collect all function applications and generate consistency lemmas
   * accordingly */
  std::vector<TNode> to_process;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    to_process.push_back(a);
  }
  for (const TNode& a : to_process)
  {
    // std::cout << a << std::endl;
    // std::cout << a.getKind() << std::endl;
    switch (a.getKind())
    {
      // custom input just for testing
      case kind::Kind_t::EQUAL:
        dfa[1] = {};
        printDfa(dfa);

        break;
      default: break;
    }
  }

  // I AM ASSUMING THERE IS ONLY ONE ASSERTION PER FILE, WE DEAL WITH MORE LATER

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
