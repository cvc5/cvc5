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
#include <queue>
#include <string>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "util/rational.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace {

}
/* -------------------------------------------------------------------------- */

void printDfa(const std::map<int, std::vector<AutomataEdge>>& dfa)
{
  for (const auto& [state, edges] : dfa)
  {
    std::cout << state << std::endl;
    for (const auto& [endpoint, transition, acc] : edges)
    {
      std::cout << endpoint << ",trans=" << transition << ",acc=" << acc << " ";
    }
    std::cout << std::endl;
  }
}

void buildDfa(const int& initial_state,
              const std::vector<int> coefficients,
              std::map<int, std::vector<AutomataEdge>>& dfa)
{
  int number_of_coefficients = static_cast<int>(coefficients.size());
  for (const auto& e : coefficients)
  {
    std::cout << e << " ";
  }
  std::cout << std::endl;
  std::queue<int> states_to_process;
  states_to_process.push(initial_state);
  std::set<int> processed_states;
  std::map<int, std::pair<int, int>> from;

  // I am assuming number of coefficients at most 64, this is obviously not the
  // general case
  while (!states_to_process.empty())
  {
    int c = states_to_process.front();
    states_to_process.pop();
    if (processed_states.find(c) != processed_states.end())
    {
      // don't need to process it again
      continue;
    }
    processed_states.insert(c);
    dfa.insert({c, {}});
    for (int transition = 0; transition < (1 << number_of_coefficients);
         transition++)
    {
      int k = c;
      // computing k

      int transition_acc_sentinel = c;
      for (int i = 0; i < number_of_coefficients; i++)
      {
        bool condition = (1 << i) & transition;
        if (condition)
        {
          k -= coefficients.at(i);
          transition_acc_sentinel += coefficients.at(i);
        }
      }
      if (k % 2 == 0)
      {
        bool is_transition_acc = transition_acc_sentinel == 0;

        // eagerly stop dfa build cause already found a solution
        std::vector<int> transitions;
        if (is_transition_acc)
        {
          while (c != initial_state)
          {
            transitions.push_back(from.at(c).second);
            c = from.at(c).first;
          }
          std::reverse(transitions.begin(), transitions.end());

          // convert LSB to integers
          std::vector<int> ans = std::vector<int>(number_of_coefficients);
          int n = static_cast<int>(transitions.size()) - 1;

          // using last transition, I didn't add it to the vec
          for (int i = 0; i < number_of_coefficients; i++)
          {
            if ((1 << i) & transition)
            {
              ans.at(i) = 1 << n;
            }
          }

          for (const auto& t : transitions)
          {
            for (int i = 0; i < number_of_coefficients; i++)
            {
              if ((1 << i) & t)
              {
                ans.at(i) += 1 << i;
              }
            }
          }
          for (const auto& e : ans) std::cout << e << " ";
          std::cout << std::endl;
          return;
        }
        struct AutomataEdge edge = {k / 2, transition, is_transition_acc};
        dfa.at(c).push_back(edge);
        states_to_process.push(k / 2);
        if (from.find(k / 2) == from.end())
        {
          from.insert({k / 2, {c, transition}});
        }
      }
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
  to_process.pop_back();  // removing redundant TRUE constant

  // after preprocessing, we always have exp = c + SUMexp
  for (const TNode& a : to_process)
  {
    TNode aux = a;
    std::cout << "assertion:" << std::endl;
    std::cout << aux << std::endl;
    std::cout << "---------" << std::endl;

    int64_t c = 0;
    std::vector<std::string> vars;
    std::vector<int> A;  // I will rename this

    // first we get rid of the = exp

    TNode lhs = *aux.begin();
    if (lhs.getKind() == kind::Kind_t::MULT)
    {
      lhs = *lhs.begin();
      int64_t coef = stoi(lhs.getConst<Rational>().toString());
      A.push_back(coef);
    }
    else
    {
      // for sure it's a single var
      A.push_back(1);
    }

    // now process right side of relation
    TNode rhs = *aux.rbegin();
    for (const TNode& assertion : rhs)
    {
      if (assertion.getKind() == kind::Kind_t::MULT)
      {
        lhs = *assertion.begin();
        int64_t coef = stoi(lhs.getConst<Rational>().toString());
        A.push_back(-1 * coef);
      }
      else if (assertion.getKind() == kind::Kind_t::VARIABLE)
      {
        A.push_back(-1);
      }
      else
      {
        // for sure it's the constant C
        c = stoi(assertion.getConst<Rational>().toString());
      }
    }
    // std::cout << "A = ";
    // for (const auto& coef : A) std::cout << coef << " ";
    // std::cout << std::endl;
    // std::cout << "c = ";
    // std::cout << c << std::endl;

    buildDfa(c, A, dfa);
    // printDfa(dfa);

    A.clear();

    // I AM ASSUMING THERE IS ONLY ONE ASSERTION PER FILE, WE DEAL WITH MORE
    // LATER
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
