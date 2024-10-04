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
#include <cstdint>
#include <string>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "util/integer.h"

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
  to_process.pop_back();  // rmeoving redundant TRUE constant

  // after preprocessing, we always have exp = c + SUMexp
  for (const TNode& a : to_process)
  {
    TNode aux = a;
    std::cout << "assertion:" << std::endl;
    std::cout << aux << std::endl;
    std::cout << "---------" << std::endl;

    int64_t c;
    std::vector<std::string> vars;
    std::vector<int> A;  // I will rename this

    // first we get rid of the = exp

    TNode lhs = *aux.begin();
    if (lhs.getKind() == kind::Kind_t::EQUAL)
    {
      int64_t coef = stoi((*lhs.begin()).toString());
      A.push_back(coef);
    }
    else
    {
      // for sure it's a single var
      A.push_back(1);
    }

    // now process right side of relation
    aux = *aux.rbegin();
    for (const TNode& assertion : aux)
    {
      std::cout << "Assertion:" << std::endl;
      std::cout << assertion << std::endl;
      if (assertion.getKind() == kind::Kind_t::MULT)
      {
        std::cout << "Its mult!\n";
        lhs = *assertion.begin();
        std::cout << lhs.toString() << std::endl;

        // int64_t coef = lhs.getConst<Integer>();
        std::cout << lhs.getKind() << std::endl;
        auto coef = lhs.getConst<Integer>();
        std::cout << coef << std::endl;
        // A.push_back(-1 * coef);
      }
      else if (assertion.getKind() == kind::Kind_t::VARIABLE)
      {
        A.push_back(-1);
      }
      else
      {
        // for sure it's the constant
        c = stoi(assertion.toString());
      }
    }

    // I AM ASSUMING THERE IS ONLY ONE ASSERTION PER FILE, WE DEAL WITH MORE
    // LATER
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
