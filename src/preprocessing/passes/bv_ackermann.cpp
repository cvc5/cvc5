/*********************                                                        */
/*! \file bv_ackermann.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Ackermannization preprocessing pass.
 **
 ** This implements the Ackermannization preprocessing pass, which enables
 ** very limited theory combination support for eager bit-blasting via
 ** Ackermannization. It reduces constraints over the combination of the
 ** theories of fixed-size bit-vectors and uninterpreted functions as
 ** described in
 **   Liana Hadarean, An Efficient and Trustworthy Theory Solver for
 **   Bit-vectors in Satisfiability Modulo Theories.
￼**   https://cs.nyu.edu/media/publications/hadarean_liana.pdf
 **/

#include "preprocessing/passes/bv_ackermann.h"

#include "expr/node.h"
#include "options/bv_options.h"
#include "theory/bv/theory_bv_utils.h"

#include <stack>
#include <unordered_set>

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace
{

void addLemmaForPair(TNode args1,
                     TNode args2,
                     const TNode func,
                     AssertionPipeline* assertionsToPreprocess,
                     NodeManager* nm,
                     std::stack<TNode>* stack)
{
  Node args_eq;

  if (args1.getKind() == kind::APPLY_UF)
  {
    AlwaysAssert(args1.getOperator() == func);
    AlwaysAssert(args2.getKind() == kind::APPLY_UF
                 && args2.getOperator() == func);
    AlwaysAssert(args1.getNumChildren() == args2.getNumChildren());

    std::vector<Node> eqs(args1.getNumChildren());

    for (unsigned i = 0, n = args1.getNumChildren(); i < n; ++i)
    {
      eqs[i] = nm->mkNode(kind::EQUAL, args1[i], args2[i]);
    }
    args_eq = bv::utils::mkAnd(eqs);
  }
  else
  {
    AlwaysAssert(args1.getKind() == kind::SELECT && args1[0] == func);
    AlwaysAssert(args2.getKind() == kind::SELECT && args2[0] == func);
    AlwaysAssert(args1.getNumChildren() == 2);
    AlwaysAssert(args2.getNumChildren() == 2);
    args_eq = nm->mkNode(kind::EQUAL, args1[1], args2[1]);
  }
  Node func_eq = nm->mkNode(kind::EQUAL, args1, args2);
  Node lemma = nm->mkNode(kind::IMPLIES, args_eq, func_eq);
  assertionsToPreprocess->push_back(lemma);
  /* add the constraint to the stack so that
  * collectFunctionsAndLemmas will process it as well. */
}

void storeFunctionAndAddLemmas(TNode func,
                               TNode term,
                               FunctionToArgsMap& fun_to_args,
                               SubstitutionMap& fun_to_skolem,
                               AssertionPipeline* assertions,
                               NodeManager* nm,
                               std::stack<TNode>* stack)
{
  if (fun_to_args.find(func) == fun_to_args.end())
  {
    fun_to_args.insert(make_pair(func, NodeSet()));
  }
  NodeSet& set = fun_to_args[func];
  if (set.find(term) == set.end())
  {
    TypeNode tn = term.getType();
    Node skolem = nm->mkSkolem(
        "BVSKOLEM$$",
        tn,
        "is a variable created by the ackermannization "
        "preprocessing pass for theory BV");
    for (const auto& t : set)
    {
      addLemmaForPair(t, term, func, assertions, nm, stack);
    }
    set.insert(term);
    fun_to_skolem.addSubstitution(term, skolem);
    for (TNode arg : term)
    {
      stack->push(arg);
    }
  }
}

/* We only add top-level applications of functions.
 * For example: when we see "f(g(x))", we do not add g as a function and x as a
 * parameter.
 * Instead, we only include f as a function and g(x) as a parameter.
 * However, if we see g(x) later on as a top-level application, we will add it
 * as well.
 * Another example: for the formula f(g(x))=f(g(y)),
 * we first only add f as a function and g(x),g(y) as arguments.
 * storeFunctionAndAddLemmas will then add the constraint g(x)=g(y) ->
 * f(g(x))=f(g(y)).
 * Now that we see g(x) and g(y), we explicitly add them as well. */
void collectFunctionsAndLemmas(FunctionToArgsMap& fun_to_args,
                               SubstitutionMap& fun_to_skolem,
                               std::stack<TNode>* stack,
                               AssertionPipeline* assertions)
{
  std::unordered_set<TNode, TNodeHashFunction> seen;       
  NodeManager* nm = NodeManager::currentNM();
  TNode term;
  while (!stack->empty())
  {
    term = stack->top();
    stack->pop();
    if (seen.find(term) == seen.end())
    {
        TNode func;
        if (term.getKind() == kind::APPLY_UF)
        {
          storeFunctionAndAddLemmas(term.getOperator(),
                                    term,
                                    fun_to_args,
                                    fun_to_skolem,
                                    assertions,
                                    nm,
                                    stack);
        }
        else if (term.getKind() == kind::SELECT)
        {
          storeFunctionAndAddLemmas(
              term[0], term, fun_to_args, fun_to_skolem, assertions, nm, stack);
        }
        else
        {
          AlwaysAssert(
              term.getKind() != kind::STORE,
              "Cannot use eager bitblasting on QF_ABV formula with stores");
          /* add childrens to the stack, so that they are processed later 
           * do this only for childred that weren't already processed. */
          for (const TNode& n : term)
          {
            stack->push(n);
          }
        }
    seen.insert(term);
    }
  }
}

}  // namespace

/* -------------------------------------------------------------------------- */

BVAckermann::BVAckermann(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-ackermann"),
      d_funcToSkolem(preprocContext->getUserContext())
{
}

PreprocessingPassResult BVAckermann::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER);
  AlwaysAssert(!options::incrementalSolving());

  /* collect all function applications and generate consistency lemmas
   * accordingly */
  std::stack<TNode> to_process;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    to_process.push(a);
  }
  collectFunctionsAndLemmas(
      d_funcToArgs, d_funcToSkolem, &to_process, assertionsToPreprocess);

  /* replace applications of UF by skolems */
  // FIXME for model building, github issue #1901
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i, d_funcToSkolem.apply((*assertionsToPreprocess)[i]));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
