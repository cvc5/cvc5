/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for checking for illegal inputs
 */

#include "smt/illegal_checker.h"

#include "base/modal_exception.h"
#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/bags_options.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/ff_options.h"
#include "options/fp_options.h"
#include "options/main_options.h"
#include "options/sets_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "smt/env.h"
#include "smt/logic_exception.h"

namespace cvc5::internal {
namespace smt {

IllegalChecker::IllegalChecker(Env& e)
    : EnvObj(e), d_assertionIndex(userContext(), 0)
{
  d_checkFreeVar = language::isLangSygus(options().base.inputLanguage);

  // Determine any illegal kinds that are dependent on options that need to be
  // guarded here. Note that nearly all illegal kinds should be properly guarded
  // by either the theory engine, theory solvers, or by theory rewriters. We
  // only require special handling for rare cases, including array constants,
  // where array constants *must* be rewritten by the rewriter for the purposes
  // of model verification, but we do not want array constants to appear in
  // assertions unless --arrays-exp is enabled.

  // Array constants are not supported unless arraysExp is enabled
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_ARRAYS)
      && !options().arrays.arraysExp)
  {
    d_illegalKinds.insert(Kind::STORE_ALL);
  }
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_ARITH)
      && !options().arith.arithExp)
  {
    d_illegalKinds.insert(Kind::PI);
    d_illegalKinds.insert(Kind::EXPONENTIAL);
    d_illegalKinds.insert(Kind::SINE);
    d_illegalKinds.insert(Kind::COSINE);
    d_illegalKinds.insert(Kind::TANGENT);
    d_illegalKinds.insert(Kind::COSECANT);
    d_illegalKinds.insert(Kind::SECANT);
    d_illegalKinds.insert(Kind::COTANGENT);
    d_illegalKinds.insert(Kind::ARCSINE);
    d_illegalKinds.insert(Kind::ARCCOSINE);
    d_illegalKinds.insert(Kind::ARCTANGENT);
    d_illegalKinds.insert(Kind::ARCCOSECANT);
    d_illegalKinds.insert(Kind::ARCSECANT);
    d_illegalKinds.insert(Kind::ARCCOTANGENT);
    d_illegalKinds.insert(Kind::SQRT);
    d_illegalKinds.insert(Kind::IAND);
    d_illegalKinds.insert(Kind::POW2);
  }
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_DATATYPES)
      && !options().datatypes.datatypesExp)
  {
    d_illegalKinds.insert(Kind::MATCH);
  }
  if (!logicInfo().hasCardinalityConstraints() && !options().uf.ufCardExp)
  {
    d_illegalKinds.insert(Kind::CARDINALITY_CONSTRAINT);
  }
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_SETS))
  {
    if (!options().sets.setsCardExp)
    {
      d_illegalKinds.insert(Kind::SET_CARD);
    }
    if (!options().sets.relsExp)
    {
      d_illegalKinds.insert(Kind::RELATION_TABLE_JOIN);
      d_illegalKinds.insert(Kind::RELATION_TRANSPOSE);
      d_illegalKinds.insert(Kind::RELATION_PRODUCT);
      d_illegalKinds.insert(Kind::RELATION_JOIN);
      d_illegalKinds.insert(Kind::RELATION_TCLOSURE);
      d_illegalKinds.insert(Kind::RELATION_IDEN);
      d_illegalKinds.insert(Kind::RELATION_JOIN_IMAGE);
      d_illegalKinds.insert(Kind::RELATION_GROUP);
      d_illegalKinds.insert(Kind::RELATION_AGGREGATE);
      d_illegalKinds.insert(Kind::RELATION_PROJECT);
    }
  }
  // unsupported theories disables all kinds belonging to the
  std::unordered_set<theory::TheoryId> unsupportedTheories;
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_FP)
      && !options().fp.fp)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_FP);
  }
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_FF)
      && !options().ff.ff)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_FF);
  }
  if (logicInfo().isTheoryEnabled(internal::theory::THEORY_BAGS)
      && !options().bags.bags)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_BAGS);
  }
}

void IllegalChecker::checkAssertions(Assertions& as)
{
  // check illegal kinds here
  const context::CDList<Node>& assertions = as.getAssertionList();
  size_t asize = assertions.size();
  size_t i = d_assertionIndex.get();
  std::unordered_set<TNode> visited;
  while (i < asize)
  {
    Node n = assertions[i];
    i++;
    if (!d_illegalKinds.empty())
    {
      Kind k = expr::hasSubtermKinds(d_illegalKinds, n, visited);
      if (k != Kind::UNDEFINED_KIND)
      {
        std::stringstream ss;
        ss << "ERROR: cannot handle assertion with term of kind " << k
           << " in this configuration";
        if (k == Kind::STORE_ALL)
        {
          ss << ", unless --arrays-exp is enabled";
        }
        throw LogicException(ss.str());
      }
    }
    // Ensure that it does not contain free variables
    if (d_checkFreeVar)
    {
      // Note that API users and the smt2 parser may generate assertions with
      // shadowed variables, which are resolved during rewriting. Hence we do
      // not check for this here.
      if (expr::hasFreeVar(n))
      {
        std::stringstream se;
        se << "Cannot process assertion with free variable.";
        if (language::isLangSygus(options().base.inputLanguage))
        {
          // Common misuse of SyGuS is to use top-level assert instead of
          // constraint when defining the synthesis conjecture.
          se << " Perhaps you meant `constraint` instead of `assert`?";
        }
        throw ModalException(se.str().c_str());
      }
    }
  }
  d_assertionIndex = asize;
}

}  // namespace smt
}  // namespace cvc5::internal
