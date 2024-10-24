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
#include <optional>
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
              std::map<int, std::vector<AutomataEdge>>& dfa,
              const kind::Kind_t& assertion_kind,
              int mod_value)
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

  // I am assuming number of coefficients at most 64, this is obviously not
  // the general case
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
      switch (assertion_kind)
      {
        case kind::Kind_t::EQUAL:
        {
          if (k % 2 == 0)
          {
            bool is_transition_acc = transition_acc_sentinel == 0;
            struct AutomataEdge edge = {k / 2, transition, is_transition_acc};
            dfa.at(c).push_back(edge);
            states_to_process.push(k / 2);
          }

          break;
        }
        case kind::Kind_t::LEQ:
        {
          bool is_transition_acc = transition_acc_sentinel >= 0;
          int new_state = k % 2 == 0 ? k / 2 : (k < 0 ? k / 2 - 1 : k / 2);
          std::cout << "--------" << std::endl;
          std::cout << k << std::endl;
          std::cout << new_state << std::endl;
          std::cout << "--------" << std::endl;
          struct AutomataEdge edge = {new_state, transition, is_transition_acc};
          dfa.at(c).push_back(edge);
          states_to_process.push(new_state);
          break;
        };
        case kind::Kind_t::INTS_MODULUS_TOTAL:
        {
          if (mod_value % 2 == 0)
          {
            if (k % 2 == 0)
            {
              bool is_transition_acc = transition_acc_sentinel % mod_value == 0;
              int new_state = (mod_value + ((k / 2) % mod_value)) % mod_value;
              struct AutomataEdge edge = {
                  new_state, transition, is_transition_acc};
              dfa.at(c).push_back(edge);
              states_to_process.push(new_state);
            }
          }
          else
          {
          }

          break;
        }
        default:
        {
          std::cout << "Not LIA" << std::endl;
          break;
        }
      }
    }
  }
}

// to_process.pop_back();  // removing redundant TRUE constant
//
// // after preprocessing, we always have exp = c + SUMexp
// for (const TNode& a : to_process)
// {
//   TNode aux = a;
//   int c = 0;
//   int mod_value = 0;
//   std::vector<std::string> vars;
//   std::vector<int> coefficients;
//   kind::Kind_t assertion_kind = kind::Kind_t::EQUAL;
//
//   switch (aux.getKind())
//   {
//     case kind::Kind_t::EQUAL:
//     {
//       if ((*aux.begin()).getKind() == kind::Kind_t::INTS_MODULUS_TOTAL)
//       {
//         assertion_kind = kind::Kind_t::INTS_MODULUS_TOTAL;
//       }
//       else
//       {
//         assertion_kind = kind::Kind_t::EQUAL;
//       }
//       break;
//     }
//     case kind::Kind_t::NOT:
//     {
//       assertion_kind = kind::Kind_t::LEQ;
//       break;
//     }
//     default: break;
//   }
//
//   // preprocessing to get coefficients of every formula. Each kind has a
//   // different format in cvc5 after preprocessing
//   switch (assertion_kind)
//   {
//     // case a1x1 + ... anxn = c
//     case kind::Kind_t::EQUAL:
//     {
//       TNode lhs = *aux.begin();
//       if (lhs.getKind() == kind::Kind_t::MULT)
//       {
//         lhs = *lhs.begin();
//         int64_t coef = stoi(lhs.getConst<Rational>().toString());
//         coefficients.push_back(coef);
//       }
//       else
//       {
//         // for sure it's a single var
//         coefficients.push_back(1);
//       }
//
//       // now process right side of relation
//       TNode rhs = *aux.rbegin();
//       for (const TNode& assertion : rhs)
//       {
//         if (assertion.getKind() == kind::Kind_t::MULT)
//         {
//           lhs = *assertion.begin();
//           int64_t coef = stoi(lhs.getConst<Rational>().toString());
//           coefficients.push_back(-1 * coef);
//         }
//         else if (assertion.getKind() == kind::Kind_t::VARIABLE)
//         {
//           coefficients.push_back(-1);
//         }
//         else
//         {
//           // for sure it's the constant C
//           c = stoi(assertion.getConst<Rational>().toString());
//         }
//       }
//       break;
//     }
//       // case a1x1 + ... + anxn <= c (cvc5 converts into a not (>=))
//     case kind::Kind_t::NOT:
//     {
//       aux = *aux.begin();
//       TNode lhs = *aux.begin();
//       TNode rhs = *(aux.end() - 1);
//       c = stoi(rhs.getConst<Rational>().toString());
//       c--;
//       for (const TNode& assertion : lhs)
//       {
//         if (assertion.getKind() == kind::Kind_t::MULT)
//         {
//           lhs = *assertion.begin();
//           int64_t coef = stoi(lhs.getConst<Rational>().toString());
//           coefficients.push_back(coef);
//         }
//         else if (assertion.getKind() == kind::Kind_t::VARIABLE)
//         {
//           coefficients.push_back(1);
//         }
//         else
//         {
//           std::cout << "We shouldn't get here" << std::endl;
//         }
//       }
//       break;
//     }
//     case kind::Kind_t::INTS_MODULUS_TOTAL:
//     {
//       TNode lhs = *aux.begin();   // the mod part
//       TNode rhs = *aux.rbegin();  // c
//       c = stoi(rhs.getConst<Rational>().toString());
//
//       rhs = *lhs.rbegin();
//       lhs = *lhs.begin();
//       mod_value = stoi(rhs.getConst<Rational>().toString());
//       for (const TNode& assertion : lhs)
//       {
//         if (assertion.getKind() == kind::Kind_t::MULT)
//         {
//           lhs = *assertion.begin();
//           int64_t coef = stoi(lhs.getConst<Rational>().toString());
//           coefficients.push_back(coef);
//         }
//         else if (assertion.getKind() == kind::Kind_t::VARIABLE)
//         {
//           coefficients.push_back(1);
//         }
//         else
//         {
//           std::cout << "We shouldn't get here" << std::endl;
//         }
//       }
//       break;
//     }
//     default: break;
//   }
//
//   buildDfa(c, coefficients, dfa, assertion_kind, mod_value);
//   printDfa(dfa);
//
//   coefficients.clear();
//
//   // I AM ASSUMING THERE IS ONLY ONE ASSERTION PER FILE, WE DEAL WITH MORE
//   // LATER
// }

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
  for (const auto& e : to_process)
  {
    std::cout << e << std::endl;
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
