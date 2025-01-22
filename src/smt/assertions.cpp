/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "proof/lazy_proof.h"
#include "proof/proof_node_algorithm.h"
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
    if (n.getKind() == Kind::EQUAL && n[0].isVar())
    {
      Trace("smt-define-fun")
          << "Define fun: " << n[0] << " = " << n[1] << std::endl;
      NodeManager* nm = nodeManager();
      TrustSubstitutionMap& tsm = d_env.getTopLevelSubstitutions();
      // If it is a lambda, we rewrite the body, otherwise we rewrite itself.
      // For lambdas, we prefer rewriting only the body since we don't want
      // higher-order rewrites (e.g. value normalization) to apply by default.
      TrustNode defRewBody;
      // For efficiency, we only do this if it is a lambda.
      // Note this is important since some benchmarks treat define-fun as a
      // global let. We should not eagerly rewrite in these cases.
      if (n[1].getKind() == Kind::LAMBDA)
      {
        // Rewrite the body of the lambda.
        defRewBody = tsm.applyTrusted(n[1][1], d_env.getRewriter());
      }
      Node defRew = n[1];
      // If we rewrote the body
      if (!defRewBody.isNull())
      {
        // The rewritten form is the rewritten body with original variable list.
        defRew = defRewBody.getNode();
        defRew = nm->mkNode(Kind::LAMBDA, n[1][0], defRew);
      }
      // if we need to track proofs
      if (d_env.isProofProducing())
      {
        // initialize the proof generator if not already done so
        if (d_defFunRewPf == nullptr)
        {
          d_defFunRewPf = std::make_shared<LazyCDProof>(d_env);
        }
        // A define-fun is an assumption in the overall proof, thus
        // we justify the substitution with ASSUME here.
        d_defFunRewPf->addStep(n, ProofRule::ASSUME, {}, {n});
        // If changed, prove the rewrite
        if (defRew != n[1])
        {
          Node eqBody = defRewBody.getProven();
          d_defFunRewPf->addLazyStep(eqBody, defRewBody.getGenerator());
          Node eqRew = n[1].eqNode(defRew);
          Assert (n[1].getKind() == Kind::LAMBDA);
          // congruence over the binder
          std::vector<Node> cargs;
          ProofRule cr = expr::getCongRule(n[1], cargs);
          d_defFunRewPf->addStep(eqRew, cr, {eqBody}, cargs);
          // Proof is:
          //                            ------ from tsm
          //                            t = t'
          // ------------------ ASSUME  -------------------------- CONG
          // n = lambda x. t            lambda x. t = lambda x. t'
          // ------------------------------------------------------ TRANS
          // n = lambda x. t'
          Node eqFinal = n[0].eqNode(defRew);
          d_defFunRewPf->addStep(eqFinal, ProofRule::TRANS, {n, eqRew}, {});
        }
      }
      Trace("smt-define-fun") << "...rewritten to " << defRew << std::endl;
      d_env.getTopLevelSubstitutions().addSubstitution(
          n[0], defRew, d_defFunRewPf.get());
      return;
    }
  }

  // Ensure that it does not contain free variables
  if (maybeHasFv)
  {
    // Note that API users and the smt2 parser may generate assertions with
    // shadowed variables, which are resolved during rewriting. Hence we do not
    // check for this here.
    if (expr::hasFreeVar(n))
    {
      std::stringstream se;
      if (isFunDef)
      {
        se << "Cannot process function definition with free variable.";
      }
      else
      {
        se << "Cannot process assertion with free variable.";
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
