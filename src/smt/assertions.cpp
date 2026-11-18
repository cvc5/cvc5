/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "expr/beta_reduce_converter.h"
#include "expr/node_algorithm.h"
#include "expr/subtype_elim_node_converter.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/language.h"
#include "options/proof_options.h"
#include "options/smt_options.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node_algorithm.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/trust_substitutions.h"
#include "util/result.h"

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

namespace {

/**
 * Applies beta-reduction to all subterms, where bound variables in the body
 * of a lambda are renamed beforehand if necessary to avoid shadowing and
 * variable capture. For example, beta reducing
 *   (_ (lambda y. exists x. (distinct x y)) x)
 * with a plain substitution would capture x, whereas this converter first
 * renames the bound variable x in the body of the lambda.
 */
class CaptureAvoidingBetaReduceConverter : public BetaReduceNodeConverter
{
 public:
  CaptureAvoidingBetaReduceConverter(NodeManager* nm, Rewriter* rr)
      : BetaReduceNodeConverter(nm), d_rr(rr)
  {
  }
  Node postConvert(Node n) override
  {
    if (n.getKind() == Kind::APPLY_UF
        && n.getOperator().getKind() == Kind::LAMBDA)
    {
      // Apply the same renaming as the rewriter does prior to beta reduction.
      // This may apply more than once, e.g. first to eliminate shadowing of
      // the variables of the lambda, then to avoid capturing the free
      // variables of the arguments.
      Node nes;
      while (!(nes = d_rr->rewriteViaRule(
                   ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID, n))
                  .isNull())
      {
        n = nes;
      }
    }
    return BetaReduceNodeConverter::postConvert(n);
  }

 private:
  /** The rewriter, used for renaming bound variables */
  Rewriter* d_rr;
};

}  // namespace

Assertions::Assertions(Env& env)
    : EnvObj(env),
      d_assertionList(userContext()),
      d_assertionListDefs(userContext()),
      d_macroDefs(userContext()),
      d_inputForm(userContext()),
      d_inputAssertionList(userContext()),
      d_globalDefineFunLemmasIndex(userContext(), 0)
{
}

Assertions::~Assertions() {}

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

const context::CDList<Node>& Assertions::getMacroDefinitions() const
{
  return d_macroDefs;
}

Node Assertions::getInputForm(const Node& n) const
{
  NodeNodeMap::const_iterator it = d_inputForm.find(n);
  if (it != d_inputForm.end())
  {
    return (*it).second;
  }
  return n;
}

const context::CDList<Node>& Assertions::getInputAssertionList() const
{
  return options().proof.proofDefineFunMacros ? d_inputAssertionList
                                              : d_assertionList;
}

std::unordered_set<Node> Assertions::getCurrentAssertionListDefitions() const
{
  std::unordered_set<Node> defSet;
  for (const Node& a : d_assertionListDefs)
  {
    defSet.insert(a);
  }
  // definitions treated as macros are definitions as well
  for (const Node& a : d_macroDefs)
  {
    defSet.insert(a);
  }
  return defSet;
}

void Assertions::addFormula(TNode n, bool isFunDef, bool maybeHasFv)
{
  // The assertion, after expanding definitions that are treated as macros.
  Node nn = n;
  if (options().proof.proofDefineFunMacros)
  {
    if (!isFunDef)
    {
      // Ensure that global definitions have been processed, e.g. after a user
      // pop, so that their applications can be expanded below. This is a no-op
      // if all global definitions have been processed in this context.
      refresh();
    }
    // Expand the applications of the definitions we have processed so far.
    // Note this applies to the bodies of definitions as well.
    nn = applyDefinitions(n);
    // Remember the input form of all assertions, including definitions.
    d_inputAssertionList.push_back(n);
    if (isFunDef && addMacroDefinition(nn))
    {
      // The definition was processed as a macro, in which case it is not an
      // assertion, and hence will not appear as an assumption in proofs.
      return;
    }
    if (nn != n)
    {
      // Remember the input form of this assertion, which is used e.g. when
      // reporting unsat cores and the result of get-assertions.
      if (d_inputForm.find(nn) == d_inputForm.end())
      {
        d_inputForm.insert(nn, n);
      }
    }
  }
  // add to assertion list
  d_assertionList.push_back(nn);
  if (nn.isConst() && nn.getConst<bool>())
  {
    // true, nothing to do
    return;
  }
  Trace("smt") << "Assertions::addFormula(" << nn << ", isFunDef = " << isFunDef
               << std::endl;
  // In non-incremental, we treat higher-order equality as define-fun
  if (!options().base.incrementalSolving || isFunDef)
  {
    // if a non-recursive define-fun, just add as a top-level substitution
    if (nn.getKind() == Kind::EQUAL && nn[0].isVar())
    {
      Trace("smt-define-fun")
          << "Define fun: " << nn[0] << " = " << nn[1] << std::endl;
      NodeManager* nm = nodeManager();
      TrustSubstitutionMap& tsm = d_env.getTopLevelSubstitutions();
      if (!isFunDef
          && (tsm.get().hasSubstitution(nn[0])
              || nn[1].getKind() != Kind::LAMBDA))
      {
        return;
      }
      // If it is a lambda, we rewrite the body, otherwise we rewrite itself.
      // For lambdas, we prefer rewriting only the body since we don't want
      // higher-order rewrites (e.g. value normalization) to apply by default.
      TrustNode defRewBody;
      // For efficiency, we only do this if it is a lambda.
      // Note this is important since some benchmarks treat define-fun as a
      // global let. We should not eagerly rewrite in these cases.
      if (nn[1].getKind() == Kind::LAMBDA)
      {
        // Rewrite the body of the lambda.
        defRewBody = tsm.applyTrusted(nn[1][1], d_env.getRewriter());
      }
      Node defRew = nn[1];
      // If we rewrote the body
      if (!defRewBody.isNull())
      {
        // The rewritten form is the rewritten body with original variable list.
        defRew = defRewBody.getNode();
        defRew = nm->mkNode(Kind::LAMBDA, nn[1][0], defRew);
      }
      if (expr::hasSubterm(defRew, nn[0]))
      {
        return;
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
        d_defFunRewPf->addStep(nn, ProofRule::ASSUME, {}, {nn});
        // If changed, prove the rewrite
        if (defRew != nn[1])
        {
          Node eqBody = defRewBody.getProven();
          d_defFunRewPf->addLazyStep(eqBody, defRewBody.getGenerator());
          Node eqRew = nn[1].eqNode(defRew);
          Assert(nn[1].getKind() == Kind::LAMBDA);
          // congruence over the binder
          std::vector<Node> cargs;
          ProofRule cr = expr::getCongRule(nn[1], cargs);
          d_defFunRewPf->addStep(eqRew, cr, {eqBody}, cargs);
          // Proof is:
          //                            ------ from tsm
          //                            t = t'
          // ------------------ ASSUME  -------------------------- CONG
          // n = lambda x. t            lambda x. t = lambda x. t'
          // ------------------------------------------------------ TRANS
          // n = lambda x. t'
          Node eqFinal = nn[0].eqNode(defRew);
          d_defFunRewPf->addStep(eqFinal, ProofRule::TRANS, {nn, eqRew}, {});
        }
      }
      Trace("smt-define-fun") << "...rewritten to " << defRew << std::endl;
      d_assertionListDefs.push_back(nn);
      d_env.getTopLevelSubstitutions().addSubstitution(
          nn[0], defRew, d_defFunRewPf.get());
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

bool Assertions::addMacroDefinition(const Node& n)
{
  Assert(options().proof.proofDefineFunMacros);
  if (n.getKind() != Kind::EQUAL || !n[0].isVar())
  {
    // e.g. a (mutually) recursive function definition, which is not a macro
    return false;
  }
  if (expr::hasSubterm(n[1], n[0]))
  {
    // a recursive definition cannot be expanded
    return false;
  }
  Trace("smt-define-fun") << "Macro definition: " << n[0] << " = " << n[1]
                          << std::endl;
  // Note that we do not rewrite the body of the definition here, in contrast
  // to definitions that are treated as assumptions. This ensures that
  // expanding it coincides with how a proof checker expands the definition
  // as a macro, e.g. Ethos with --reference-define-fun.
  if (d_defSubs == nullptr)
  {
    d_defSubs.reset(new theory::SubstitutionMap(userContext()));
  }
  d_defSubs->addSubstitution(n[0], n[1]);
  // Add to the top-level substitutions, where notably we do not track the
  // substitution for proofs. The definition is not an assumption of the
  // proof, since its applications have been expanded in all assertions.
  // Hence it should never be applied to a formula we require a proof for. It
  // is added to the top-level substitutions so that it is expanded in terms
  // from the user, e.g. for get-value.
  d_env.getTopLevelSubstitutions().addSubstitution(n[0], n[1], nullptr, false);
  // Remember the definition, e.g. for checking unsat cores.
  d_macroDefs.push_back(n);
  return true;
}

Node Assertions::applyDefinitions(TNode n)
{
  if (d_defSubs == nullptr || d_defSubs->empty())
  {
    return n;
  }
  Node ns = d_defSubs->apply(n);
  if (ns != n)
  {
    // Eliminate beta redexes introduced by expanding applications of defined
    // functions. Note we do not rewrite here, since the expanded assertion
    // should remain as close as possible to the input assertion. Bound
    // variables are only renamed when necessary to avoid shadowing or
    // variable capture.
    CaptureAvoidingBetaReduceConverter brc(nodeManager(), d_env.getRewriter());
    ns = brc.convert(ns);
  }
  return ns;
}

void Assertions::addDefineFunDefinition(Node n, bool global)
{
  if (global)
  {
    // Global definitions are asserted at check-sat-time because we have to
    // make sure that they are always present
    Assert(!language::isLangSygus(options().base.inputLanguage));
    d_globalDefineFunLemmas.emplace_back(n);
    if (options().proof.proofDefineFunMacros)
    {
      // If definitions are treated as macros, we must process the definition
      // immediately, since it must be expanded in subsequent assertions and
      // definitions. Note that refresh will process this definition again
      // if the current user context is popped.
      refresh();
    }
  }
  else
  {
    if (options().proof.proofDefineFunMacros)
    {
      // Ensure that global definitions have been processed, e.g. after a
      // user pop, so that they can be expanded in the body of this
      // definition.
      refresh();
    }
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
