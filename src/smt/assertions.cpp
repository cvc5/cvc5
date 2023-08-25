/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for storing assertions for an SMT engine.
 */

#include "smt/assertions.h"

#include <sstream>

#include "base/modal_exception.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "theory/trust_substitutions.h"
#include "util/result.h"

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

Assertions::Assertions(Env& env)
    : EnvObj(env),
      d_assertionList(userContext()),
      d_assertionListDefs(userContext()),
      d_globalDefineFunLemmasIndex(userContext(), 0)
{
}

Assertions::~Assertions()
{
}

void Assertions::refresh()
{
  // Global definitions are asserted now to ensure they always exist. This is
  // done at the beginning of preprocessing, to ensure that definitions take
  // priority over, e.g. solving during preprocessing. See issue #7479.
  size_t numGlobalDefs = d_globalDefineFunLemmas.size();
  for (size_t i = d_globalDefineFunLemmasIndex.get(); i < numGlobalDefs; i++)
  {
    addFormula(d_globalDefineFunLemmas[i], true, false);
  }
  d_globalDefineFunLemmasIndex = numGlobalDefs;
}

void Assertions::setAssumptions(const std::vector<Node>& assumptions)
{
  d_assumptions.clear();
  d_assumptions = assumptions;

  for (const Node& n : d_assumptions)
  {
    // Ensure expr is type-checked at this point.
    ensureBoolean(n);
    addFormula(n, false, false);
  }
}

void Assertions::assertFormula(const Node& n)
{
  ensureBoolean(n);
  bool maybeHasFv = language::isLangSygus(options().base.inputLanguage);
  addFormula(n, false, maybeHasFv);
}

std::vector<Node>& Assertions::getAssumptions() { return d_assumptions; }

const context::CDList<Node>& Assertions::getAssertionList() const
{
  return d_assertionList;
}

const context::CDList<Node>& Assertions::getAssertionListDefinitions() const
{
  return d_assertionListDefs;
}

std::unordered_set<Node> Assertions::getCurrentAssertionListDefitions() const
{
  std::unordered_set<Node> defSet;
  for (const Node& a : d_assertionListDefs)
  {
    defSet.insert(a);
  }
  return defSet;
}

void Assertions::addFormula(TNode n,
                            bool isFunDef,
                            bool maybeHasFv)
{
  // add to assertion list
  d_assertionList.push_back(n);
  if (isFunDef)
  {
    d_assertionListDefs.push_back(n);
  }
  if (n.isConst() && n.getConst<bool>())
  {
    // true, nothing to do
    return;
  }
  Trace("smt") << "Assertions::addFormula(" << n
               << ", isFunDef = " << isFunDef << std::endl;
  if (isFunDef)
  {
    // if a non-recursive define-fun, just add as a top-level substitution
    if (n.getKind() == EQUAL && n[0].isVar())
    {
      // A define-fun is an assumption in the overall proof, thus
      // we justify the substitution with ASSUME here.
      d_env.getTopLevelSubstitutions().addSubstitution(
          n[0], n[1], PfRule::ASSUME, {}, {n});
      return;
    }
  }

  // Ensure that it does not contain free variables
  if (maybeHasFv)
  {
    bool wasShadow = false;
    if (expr::hasFreeOrShadowedVar(n, wasShadow))
    {
      std::string varType(wasShadow ? "shadowed" : "free");
      std::stringstream se;
      if (isFunDef)
      {
        se << "Cannot process function definition with " << varType
           << " variable.";
      }
      else
      {
        se << "Cannot process assertion with " << varType << " variable.";
        if (language::isLangSygus(options().base.inputLanguage))
        {
          // Common misuse of SyGuS is to use top-level assert instead of
          // constraint when defining the synthesis conjecture.
          se << " Perhaps you meant `constraint` instead of `assert`?";
        }
      }
      throw ModalException(se.str().c_str());
    }
  }
}

void Assertions::addDefineFunDefinition(Node n, bool global)
{
  if (global)
  {
    // Global definitions are asserted at check-sat-time because we have to
    // make sure that they are always present
    Assert(!language::isLangSygus(options().base.inputLanguage));
    d_globalDefineFunLemmas.emplace_back(n);
  }
  else
  {
    // We don't permit functions-to-synthesize within recursive function
    // definitions currently. Thus, we should check for free variables if the
    // input language is SyGuS.
    bool maybeHasFv = language::isLangSygus(options().base.inputLanguage);
    addFormula(n, true, maybeHasFv);
  }
}

void Assertions::ensureBoolean(const Node& n)
{
  TypeNode type = n.getType(options().expr.typeChecking);
  if (!type.isBoolean())
  {
    std::stringstream ss;
    ss << "Expected Boolean type\n"
       << "The assertion : " << n << "\n"
       << "Its type      : " << type;
    throw TypeCheckingExceptionPrivate(n, ss.str());
  }
}

}  // namespace smt
}  // namespace cvc5::internal
