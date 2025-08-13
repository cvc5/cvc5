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

#include <unordered_set>

#include "base/modal_exception.h"
#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/bags_options.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/ff_options.h"
#include "options/fp_options.h"
#include "options/main_options.h"
#include "options/sep_options.h"
#include "options/sets_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "smt/env.h"
#include "smt/logic_exception.h"

namespace cvc5::internal {
namespace smt {

IllegalChecker::IllegalChecker(Env& e)
    : EnvObj(e), d_visited(userContext()), d_assertionIndex(userContext(), 0)
{
  // Determine any illegal kinds that are dependent on options that need to be
  // guarded here. Note that nearly all illegal kinds should be properly guarded
  // by either the theory engine, theory solvers, or by theory rewriters. We
  // only require special handling for rare cases, including array constants,
  // where array constants *must* be rewritten by the rewriter for the purposes
  // of model verification, but we do not want array constants to appear in
  // assertions unless --arrays-exp is enabled.

  // Note that we don't guard against HO_APPLY, since it can naturally be
  // handled in proofs.

  // Array constants are not supported unless arraysExp is enabled
  if (logicInfo().isTheoryEnabled(theory::THEORY_ARRAYS)
      && !options().arrays.arraysExp)
  {
    d_illegalKinds.insert(Kind::STORE_ALL);
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_ARITH)
      && !options().arith.arithExp)
  {
    d_illegalKinds.insert(Kind::POW);
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
  if (logicInfo().isTheoryEnabled(theory::THEORY_DATATYPES)
      && !options().datatypes.datatypesExp)
  {
    d_illegalKinds.insert(Kind::MATCH);
    // catches all occurrences of nullables
    d_illegalKinds.insert(Kind::NULLABLE_TYPE);
  }
  if (logicInfo().hasCardinalityConstraints() && !options().uf.ufCardExp)
  {
    d_illegalKinds.insert(Kind::CARDINALITY_CONSTRAINT);
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_SETS))
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
  // unsupported theories disables all kinds belonging to the theory
  std::unordered_set<theory::TheoryId> unsupportedTheories;
  if (logicInfo().isTheoryEnabled(theory::THEORY_FP) && !options().fp.fp)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_FP);
    // Require a special check for rounding mode
    d_illegalTypes.insert(nodeManager()->roundingModeType());
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_FF) && !options().ff.ff)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_FF);
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_BAGS) && !options().bags.bags)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_BAGS);
  }
  if (logicInfo().isTheoryEnabled(theory::THEORY_SEP) && !options().sep.sep)
  {
    unsupportedTheories.insert(theory::TheoryId::THEORY_SEP);
  }
  if (!unsupportedTheories.empty())
  {
    for (int32_t i = 0; i < static_cast<int32_t>(Kind::LAST_KIND); ++i)
    {
      Kind k = static_cast<Kind>(i);
      // these two kinds are special cased in kindToTheoryId, skip
      if (k == Kind::UNDEFINED_KIND || k == Kind::NULL_EXPR)
      {
        continue;
      }
      theory::TheoryId tid = theory::kindToTheoryId(k);
      if (unsupportedTheories.find(tid) != unsupportedTheories.end())
      {
        d_illegalKinds.insert(k);
      }
    }
  }
}

void IllegalChecker::checkAssertions(Assertions& as)
{
  if (d_illegalKinds.empty() && d_illegalTypes.empty())
  {
    // nothing to check
    return;
  }
  // check illegal kinds here
  const context::CDList<Node>& assertions = as.getAssertionList();
  size_t asize = assertions.size();
  for (size_t i = d_assertionIndex.get(); i < asize; ++i)
  {
    Node n = assertions[i];
    Trace("illegal-check") << "Check assertion " << n << std::endl;
    Kind k = checkInternal(n);
    if (k != Kind::UNDEFINED_KIND)
    {
      std::stringstream ss;
      ss << "Cannot handle assertion with term of kind " << k
         << " in this configuration.";
      // suggested options only in non-safe builds
#ifndef CVC5_SAFE_MODE
      if (k == Kind::STORE_ALL)
      {
        ss << " Try --arrays-exp.";
      }
      else
      {
        theory::TheoryId tid = theory::kindToTheoryId(k);
        // if the kind was disabled based a theory, report it.
        switch (tid)
        {
          case theory::THEORY_FF: ss << " Try --ff."; break;
          case theory::THEORY_FP: ss << " Try --fp."; break;
          case theory::THEORY_BAGS: ss << " Try --bags."; break;
          case theory::THEORY_SEP: ss << " Try --sep."; break;
          default: break;
        }
      }
#endif
      throw SafeLogicException(ss.str());
    }
  }
  d_assertionIndex = asize;
}

Kind IllegalChecker::checkInternal(TNode n)
{
  Assert(!d_illegalKinds.empty());
  std::vector<TNode> visit;
  std::unordered_set<TypeNode> allTypes;
  TNode cur;
  visit.push_back(n);
  Kind k;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (d_visited.find(cur) == d_visited.end())
    {
      k = cur.getKind();
      if (d_illegalKinds.find(k) != d_illegalKinds.end())
      {
        return k;
      }
      else if (cur.isVar())
      {
        // check its type
        TypeNode tn = cur.getType();
        expr::getComponentTypes(tn, allTypes);
      }
      d_visited.insert(cur);
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  // now, go back and check if the types are legal
  std::vector<TypeNode> tlist(allTypes.begin(), allTypes.end());
  for (size_t i = 0; i < tlist.size(); i++)
  {
    TypeNode tn = tlist[i];
    // Must additionally get the subfield types from datatypes.
    if (tn.isDatatype())
    {
      const DType& dt = tn.getDType();
      std::unordered_set<TypeNode> sftypes = dt.getSubfieldTypes();
      std::unordered_set<TypeNode> sfctypes;
      // get the component types of each of the subfield types
      for (const TypeNode& sft : sftypes)
      {
        // as an optimization, if we've already considered this type, don't
        // have to find its component types
        if (allTypes.find(sft) == allTypes.end())
        {
          expr::getComponentTypes(sft, sfctypes);
        }
      }
      for (const TypeNode& sft : sfctypes)
      {
        if (allTypes.find(sft) == allTypes.end())
        {
          tlist.emplace_back(sft);
          allTypes.insert(sft);
        }
      }
    }
    k = tn.getKind();
    if (d_illegalKinds.find(k) != d_illegalKinds.end()
        || d_illegalTypes.find(tn) != d_illegalTypes.end())
    {
      std::stringstream ss;
      ss << "Cannot handle term with type " << tn << " in this configuration";
      throw SafeLogicException(ss.str());
    }
  }
  return Kind::UNDEFINED_KIND;
}

}  // namespace smt
}  // namespace cvc5::internal
