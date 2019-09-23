/*********************                                                        */
/*! \file bv_ackermann.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Aina Niemetz, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

#include "options/bv_options.h"
#include "theory/bv/theory_bv_utils.h"

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
                     NodeManager* nm)
{
  Node args_eq;

  if (args1.getKind() == kind::APPLY_UF)
  {
    Assert(args1.getOperator() == func);
    Assert(args2.getKind() == kind::APPLY_UF && args2.getOperator() == func);
    Assert(args1.getNumChildren() == args2.getNumChildren());

    std::vector<Node> eqs(args1.getNumChildren());

    for (unsigned i = 0, n = args1.getNumChildren(); i < n; ++i)
    {
      eqs[i] = nm->mkNode(kind::EQUAL, args1[i], args2[i]);
    }
    args_eq = bv::utils::mkAnd(eqs);
  }
  else
  {
    Assert(args1.getKind() == kind::SELECT && args1[0] == func);
    Assert(args2.getKind() == kind::SELECT && args2[0] == func);
    Assert(args1.getNumChildren() == 2);
    Assert(args2.getNumChildren() == 2);
    args_eq = nm->mkNode(kind::EQUAL, args1[1], args2[1]);
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
    Node skolem = nm->mkSkolem("BVSKOLEM$$",
                               tn,
                               "is a variable created by the ackermannization "
                               "preprocessing pass for theory BV");
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
      if (term.getKind() == kind::APPLY_UF)
      {
        storeFunctionAndAddLemmas(term.getOperator(),
                                  term,
                                  fun_to_args,
                                  fun_to_skolem,
                                  assertions,
                                  nm,
                                  vec);
      }
      else if (term.getKind() == kind::SELECT)
      {
        storeFunctionAndAddLemmas(
            term[0], term, fun_to_args, fun_to_skolem, assertions, nm, vec);
      }
      else
      {
        AlwaysAssert(
            term.getKind() != kind::STORE,
            "Cannot use eager bitblasting on QF_ABV formula with stores");
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

void updateUSortsCardinality(USortCardinality& usort_cardinality, TNode term)
{
  TypeNode type = term.getType();
  if (type.isSort())
  {
	if (usort_cardinality.find(type) == usort_cardinality.end())
	{
	  usort_cardinality.insert(make_pair(type, 0));
	}
	usort_cardinality[type] = usort_cardinality[type] + 1;
  }
}

void collectUSortsToBV(USortCardinality& usort_cardinality, vector<TNode>* vec, SubstitutionMap& sorts_to_skolem)
{
  for (TNode term : vec)
  {
	TypeNode type = term.getType();
	if (!type.isSort()) continue;
	TypeNode newType = bitvector(log(usort_cardinality[type] - 1) + 1);
	Node skolem = nm->mkSkolem("BVSKOLEM$$",
                               newType,
                               "is a variable created by the ackermannization "
                               "preprocessing pass for theory BV");
	sorts_to_skolem.addSubstitution(term, skolem);
  }
}


void usortsToBitVectors(USortCardinality& usort_cardinality, SubstitutionMap& sorts_to_skolem, AssertionPipeline* assertions)
{
  std::cerr << "========== debug ===========" << endl;

  std::vector<TNode> to_process;
  for (Node& a : assertions->ref())
  {
	to_process.push_back(a);
  }
  TNode term;
  for (unsigned i = 0; i < to_process.size(); ++i)
  {
	term = to_process[i];
	cerr << term.toString() << ":" << term.getType().toString() << "\t";
	Assert(term.getKind() == kind::APPLY_UF || term.getKind() == kind::SELECT || term.getKind() == kind::STORE);

	//updateUSortsCardinality(usort_cardinality, term);

	to_process.insert(to_process.end(), term.begin(), term.end());
  }

  collectUSortsToBV(usort_cardinality, to_process, sorts_to_skolem);
  
  std::cerr << endl << "======== debug end =========" << endl;
}

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
  std::vector<TNode> to_process;
  for (const Node& a : assertionsToPreprocess->ref())
  {
    to_process.push_back(a);
  }
  collectFunctionsAndLemmas(
      d_funcToArgs, d_funcToSkolem, &to_process, assertionsToPreprocess);

  /* replace applications of UF by skolems */
  // FIXME for model building, github issue #1901
  std::cerr << "========== debug ==============" << endl;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
	std::cerr << (*assertionsToPreprocess)[i].toString() << ":";
    assertionsToPreprocess->replace(
        i, d_funcToSkolem.apply((*assertionsToPreprocess)[i]));
	std::cerr << (*assertionsToPreprocess)[i].toString() << "\t";
  }
  std::cerr << endl << "========== debug end ==========" << endl;

  /* replace uninterpreted sorts to bitvector */
  usortsToBitVectors(d_usortCardinality, d_sortsToSkolem, assertionsToPreprocess);

  for (unsigned i = 0, size = assertions->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i, d_sortsToSkolem.apply((*assertionsToPreprocess)[i]));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
