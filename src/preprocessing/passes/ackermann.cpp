/*********************                                                        */
/*! \file ackermann.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng, Yoni Zohar, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

#include "preprocessing/passes/ackermann.h"
#include <cmath>
#include "base/check.h"
#include "expr/node_algorithm.h"
#include "options/options.h"

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace {

void addLemmaForPair(TNode args1,
                     TNode args2,
                     const TNode func,
                     AssertionPipeline* assertionsToPreprocess,
                     NodeManager* nm)
{
  Node args_eq;

  if (args1.getKind() == kind::APPLY_UF)
  {
    Assert(args1.getOperator() == func);
    Assert(args2.getKind() == kind::APPLY_UF && args2.getOperator() == func);
    Assert(args1.getNumChildren() == args2.getNumChildren());
    Assert(args1.getNumChildren() >= 1);

    std::vector<Node> eqs(args1.getNumChildren());

    for (unsigned i = 0, n = args1.getNumChildren(); i < n; ++i)
    {
      eqs[i] = nm->mkNode(kind::EQUAL, args1[i], args2[i]);
    }
    if (eqs.size() >= 2)
    {
      args_eq = nm->mkNode(kind::AND, eqs);
    }
    else
    {
      args_eq = eqs[0];
    }
  }
  else
  {
    Assert(args1.getKind() == kind::SELECT && args1.getOperator() == func);
    Assert(args2.getKind() == kind::SELECT && args2.getOperator() == func);
    Assert(args1.getNumChildren() == 2);
    Assert(args2.getNumChildren() == 2);
    args_eq = nm->mkNode(Kind::AND,
      nm->mkNode(kind::EQUAL, args1[0], args2[0]),
      nm->mkNode(kind::EQUAL, args1[1], args2[1])
    );
  }
  Node func_eq = nm->mkNode(kind::EQUAL, args1, args2);
  Node lemma = nm->mkNode(kind::IMPLIES, args_eq, func_eq);
  assertionsToPreprocess->push_back(lemma);
}

void storeFunctionAndAddLemmas(TNode func,
                               TNode term,
                               FunctionToArgsMap& fun_to_args,
                               SubstitutionMap& fun_to_skolem,
                               AssertionPipeline* assertions,
                               NodeManager* nm,
                               std::vector<TNode>* vec)
{
  if (fun_to_args.find(func) == fun_to_args.end())
  {
    fun_to_args.insert(make_pair(func, TNodeSet()));
  }
  TNodeSet& set = fun_to_args[func];
  if (set.find(term) == set.end())
  {
    TypeNode tn = term.getType();
    Node skolem = nm->mkSkolem("SKOLEM$$",
                               tn,
                               "is a variable created by the ackermannization "
                               "preprocessing pass");
    for (const auto& t : set)
    {
      addLemmaForPair(t, term, func, assertions, nm);
    }
    fun_to_skolem.addSubstitution(term, skolem);
    set.insert(term);
    /* Add the arguments of term (newest element in set) to the vector, so that
     * collectFunctionsAndLemmas will process them as well.
     * This is only needed if the set has at least two elements
     * (otherwise, no lemma is generated).
     * Therefore, we defer this for term in case it is the first element in the
     * set*/
    if (set.size() == 2)
    {
      for (TNode elem : set)
      {
        vec->insert(vec->end(), elem.begin(), elem.end());
      }
    }
    else if (set.size() > 2)
    {
      vec->insert(vec->end(), term.begin(), term.end());
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
                               std::vector<TNode>* vec,
                               AssertionPipeline* assertions)
{
  TNodeSet seen;
  NodeManager* nm = NodeManager::currentNM();
  TNode term;
  while (!vec->empty())
  {
    term = vec->back();
    vec->pop_back();
    if (seen.find(term) == seen.end())
    {
      TNode func;
      if (term.getKind() == kind::APPLY_UF || term.getKind() == kind::SELECT)
      {
        storeFunctionAndAddLemmas(term.getOperator(),
                                  term,
                                  fun_to_args,
                                  fun_to_skolem,
                                  assertions,
                                  nm,
                                  vec);
      }
      else
      {
        AlwaysAssert(term.getKind() != kind::STORE)
            << "Cannot use Ackermannization on formula with stores to arrays";
        /* add children to the vector, so that they are processed later */
        for (TNode n : term)
        {
          vec->push_back(n);
        }
      }
      seen.insert(term);
    }
  }
}

}  // namespace

/* -------------------------------------------------------------------------- */

/* Given a minimum capacity for an uninterpreted sort, return the size of the
 * new BV type */
size_t getBVSkolemSize(size_t capacity)
{
  return static_cast<size_t>(log2(capacity)) + 1;
}

/* Given the lowest capacity requirements for each uninterpreted sort, assign
 * a sufficient bit-vector size.
 * Populate usVarsToBVVars so that it maps variables with uninterpreted sort to
 * the fresh skolem BV variables. variables */
void collectUSortsToBV(const unordered_set<TNode, TNodeHashFunction>& vars,
                       const USortToBVSizeMap& usortCardinality,
                       SubstitutionMap& usVarsToBVVars)
{
  NodeManager* nm = NodeManager::currentNM();

  for (TNode var : vars)
  {
    TypeNode type = var.getType();
    size_t size = getBVSkolemSize(usortCardinality.at(type));
    Node skolem = nm->mkSkolem(
        "BVSKOLEM$$",
        nm->mkBitVectorType(size),
        "a variable created by the ackermannization "
        "preprocessing pass, representing a variable with uninterpreted sort "
            + type.toString() + ".");
    usVarsToBVVars.addSubstitution(var, skolem);
  }
}

/* This function returns the list of terms with uninterpreted sort in the
 * formula represented by assertions. */
std::unordered_set<TNode, TNodeHashFunction> getVarsWithUSorts(
    AssertionPipeline* assertions)
{
  std::unordered_set<TNode, TNodeHashFunction> res;

  for (const Node& assertion : assertions->ref())
  {
    std::unordered_set<TNode, TNodeHashFunction> vars;
    expr::getVariables(assertion, vars);

    for (const TNode& var : vars)
    {
      if (var.getType().isSort())
      {
        res.insert(var);
      }
    }
  }

  return res;
}

/* This is the top level of converting uninterpreted sorts to bit-vectors.
 * We count the number of different variables for each uninterpreted sort.
 * Then for each sort, we will assign a new bit-vector type with a sufficient
 * size. The size is calculated to have enough capacity, that can accommodate
 * the variables occured in the original formula. At the end, all variables of
 * uninterpreted sorts will be converted into Skolem variables of BV */
void usortsToBitVectors(const LogicInfo& d_logic,
                        AssertionPipeline* assertions,
                        USortToBVSizeMap& usortCardinality,
                        SubstitutionMap& usVarsToBVVars)
{
  std::unordered_set<TNode, TNodeHashFunction> toProcess =
      getVarsWithUSorts(assertions);

  if (toProcess.size() > 0)
  {
    /* the current version only supports BV for removing uninterpreted sorts */
    if (not d_logic.isTheoryEnabled(theory::THEORY_BV))
    {
      return;
    }

    for (TNode term : toProcess)
    {
      TypeNode type = term.getType();
      /* Update the counts for each uninterpreted sort.
       * For non-existing keys, C++ will create a new element for it, which has
       * a default 0 value, before incrementing by 1. */
      usortCardinality[type] = usortCardinality[type] + 1;
    }

    collectUSortsToBV(toProcess, usortCardinality, usVarsToBVVars);

    for (size_t i = 0, size = assertions->size(); i < size; ++i)
    {
      Node old = (*assertions)[i];
      assertions->replace(i, usVarsToBVVars.apply((*assertions)[i]));
      Trace("uninterpretedSorts-to-bv")
          << "  " << old << " => " << (*assertions)[i] << "\n";
    }
  }
}

/* -------------------------------------------------------------------------- */

Ackermann::Ackermann(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ackermann"),
      d_funcToSkolem(preprocContext->getUserContext()),
      d_usVarsToBVVars(preprocContext->getUserContext()),
      d_logic(preprocContext->getLogicInfo())
{
}

PreprocessingPassResult Ackermann::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AlwaysAssert(!options::incrementalSolving());

  /* collect all function applications and generate consistency lemmas
   * accordingly */
  std::vector<TNode> to_process;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    to_process.push_back(a);
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

  /* replace uninterpreted sorts with bit-vectors */
  usortsToBitVectors(
      d_logic, assertionsToPreprocess, d_usortCardinality, d_usVarsToBVVars);

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
