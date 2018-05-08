/*********************                                                        */
/*! \file bv_ackermann.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

#include <unordered_set>

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

/* -------------------------------------------------------------------------- */

namespace
{

void storeFunction(
    TNode func,
    TNode term,
    FunctionToArgsMap& fun_to_args,
    SubstitutionMap& fun_to_skolem)
{
  if (fun_to_args.find(func) == fun_to_args.end())
  {
    fun_to_args.insert(make_pair(func, NodeSet()));
  }
  NodeSet& set = fun_to_args[func];
  if (set.find(term) == set.end())
  {
    set.insert(term);
    Node skolem = bv::utils::mkVar(bv::utils::getSize(term));
    fun_to_skolem.addSubstitution(term, skolem);
  }
}

void collectFunctionSymbols(
    TNode term,
    FunctionToArgsMap& fun_to_args,
    SubstitutionMap& fun_to_skolem,
    std::unordered_set<TNode, TNodeHashFunction>& seen)
{
  if (seen.find(term) != seen.end()) return;
  if (term.getKind() == kind::APPLY_UF)
  {
    storeFunction(term.getOperator(), term, fun_to_args, fun_to_skolem);
  }
  else if (term.getKind() == kind::SELECT)
  {
    storeFunction(term[0], term, fun_to_args, fun_to_skolem);
  }
  else
  {
    AlwaysAssert(term.getKind() != kind::STORE,
                 "Cannot use eager bitblasting on QF_ABV formula with stores");
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i)
  {
    collectFunctionSymbols(term[i], fun_to_args, fun_to_skolem, seen);
  }
  seen.insert(term);
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

  std::vector<Node> assertions(assertionsToPreprocess->ref());
  std::unordered_set<TNode, TNodeHashFunction> seen;

  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    collectFunctionSymbols(assertions[i], d_funcToArgs, d_funcToSkolem, seen);
  }

  NodeManager* nm = NodeManager::currentNM();
  FunctionToArgsMap::const_iterator it = d_funcToArgs.begin();
  for (; it != d_funcToArgs.end(); ++it)
  {
    TNode func = it->first;
    const NodeSet& args = it->second;
    NodeSet::const_iterator it1 = args.begin();
    for (; it1 != args.end(); ++it1)
    {
      for (NodeSet::const_iterator it2 = it1; it2 != args.end(); ++it2)
      {
        TNode args1 = *it1;
        TNode args2 = *it2;
        Node args_eq;

        if (args1.getKind() == kind::APPLY_UF)
        {
          AlwaysAssert(args1.getKind() == kind::APPLY_UF
                       && args1.getOperator() == func);
          AlwaysAssert(args2.getKind() == kind::APPLY_UF
                       && args2.getOperator() == func);
          AlwaysAssert(args1.getNumChildren() == args2.getNumChildren());

          std::vector<Node> eqs(args1.getNumChildren());

          for (unsigned i = 0; i < args1.getNumChildren(); ++i)
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
        assertions.push_back(lemma);
      }
    }
  }

  // replace applications of UF by skolems (FIXME for model building)
  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    assertions[i] = d_funcToSkolem.apply(assertions[i]);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
