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
#include "expr/elim_shadow_converter.h"
#include "expr/node_algorithm.h"
#include "expr/subtype_elim_node_converter.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "proof/conv_proof_generator.h"
#include "proof/lazy_proof.h"
#include "proof/method_id.h"
#include "proof/proof_node_algorithm.h"
#include "proof/trust_id.h"
#include "smt/env.h"
#include "theory/builtin/proof_checker.h"
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
      d_globalDefineFunLemmasIndex(userContext(), 0),
      d_defQuant(userContext())
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

Node Assertions::getDefinitionQuant(const Node& def) const
{
  context::CDHashMap<Node, Node>::const_iterator it = d_defQuant.find(def);
  if (it != d_defQuant.end())
  {
    return it->second;
  }
  return Node::null();
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

void Assertions::addFormula(TNode n, bool isFunDef, bool maybeHasFv)
{
  // add to assertion list
  d_assertionList.push_back(n);
  if (n.isConst() && n.getConst<bool>())
  {
    // true, nothing to do
    return;
  }
  Trace("smt") << "Assertions::addFormula(" << n << ", isFunDef = " << isFunDef
               << std::endl;
  // In non-incremental, we treat higher-order equality as define-fun
  if (!options().base.incrementalSolving || isFunDef)
  {
    // if a non-recursive define-fun, just add as a top-level substitution
    if (n.getKind() == Kind::EQUAL && n[0].isVar())
    {
      Trace("smt-define-fun")
          << "Define fun: " << n[0] << " = " << n[1] << std::endl;
      NodeManager* nm = nodeManager();
      TrustSubstitutionMap& tsm = d_env.getTopLevelSubstitutions();
      if (!isFunDef
          && (tsm.get().hasSubstitution(n[0])
              || n[1].getKind() != Kind::LAMBDA))
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
      if (expr::hasSubterm(defRew, n[0]))
      {
        return;
      }
      // In proofs, we justify function definitions (= f (lambda x t)) by the
      // quantified formula (forall x (= (f x) t)), whose instances are used
      // for expanding applications of f. We do this only if the variables
      // of the lambda are distinct, which is required for the instances to
      // be equivalent to beta-reduction.
      bool useQuant = isFunDef && d_env.isProofProducing()
                      && options().proof.proofDefineFunQuant
                      && n[1].getKind() == Kind::LAMBDA;
      if (useQuant)
      {
        std::unordered_set<Node> vs(n[1][0].begin(), n[1][0].end());
        useQuant = vs.size() == n[1][0].getNumChildren();
      }
      // The quantified formula, before and after rewriting
      Node q, qRew;
      Node defRewPre = defRew;
      if (useQuant)
      {
        std::vector<Node> fxc{n[0]};
        fxc.insert(fxc.end(), n[1][0].begin(), n[1][0].end());
        Node fx = nm->mkNode(Kind::APPLY_UF, fxc);
        q = nm->mkNode(Kind::FORALL, n[1][0], fx.eqNode(n[1][1]));
        qRew = nm->mkNode(Kind::FORALL, n[1][0], fx.eqNode(defRew[1]));
        // Eliminate shadowing in the definition, e.g. lambda x. forall x. P(x)
        // becomes lambda x. forall y. P(y). This ensures that instances of
        // its quantified formula do not require renaming bound variables.
        // Note this coincides with how the rewriter eliminates shadowing in
        // lambdas.
        defRew = ElimShadowNodeConverter::eliminateShadow(defRew);
        Assert(defRew[0] == n[1][0]);
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
        std::vector<Node> transPremises{n};
        Node eqBody;
        // If changed, prove the rewrite
        if (defRewPre != n[1])
        {
          eqBody = defRewBody.getProven();
          d_defFunRewPf->addLazyStep(eqBody, defRewBody.getGenerator());
          Node eqRew = n[1].eqNode(defRewPre);
          Assert(n[1].getKind() == Kind::LAMBDA);
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
          transPremises.push_back(eqRew);
        }
        if (defRew != defRewPre)
        {
          // The shadowing that was eliminated above is justified by a theory
          // rewrite step. Note this is only required in proofs if f occurs
          // not fully applied.
          Node eqShadow = defRewPre.eqNode(defRew);
          Node tidn =
              builtin::BuiltinProofRuleChecker::mkTheoryIdNode(nm, THEORY_UF);
          Node rid = mkMethodId(nm, MethodId::RW_REWRITE_THEORY_POST);
          d_defFunRewPf->addStep(eqShadow,
                                 ProofRule::TRUST_THEORY_REWRITE,
                                 {},
                                 {eqShadow, tidn, rid});
          transPremises.push_back(eqShadow);
        }
        if (transPremises.size() > 1)
        {
          Node eqFinal = n[0].eqNode(defRew);
          d_defFunRewPf->addStep(eqFinal, ProofRule::TRANS, transPremises, {});
        }
        if (useQuant)
        {
          // The quantified formula is an assumption, which we transform to
          // the quantified formula for the rewritten definition:
          //
          //           ---------- REFL  ------ from tsm
          //           (f x) = (f x)    t = t'
          //           ----------------------- CONG
          //           ((f x) = t) = ((f x) = t')
          // ------ ASSUME  -------------------------------------- CONG
          // q              q = (forall x. (f x) = t')
          // ---------------------------------------------------- EQ_RESOLVE
          // forall x. (f x) = t'
          //
          // followed by EQ_RESOLVE with a step eliminating shadowing, if
          // necessary.
          d_defFunRewPf->addStep(q, ProofRule::ASSUME, {}, {q});
          Node fx = q[1][0];
          if (q != qRew)
          {
            Assert(!eqBody.isNull());
            Node fxeq = fx.eqNode(fx);
            d_defFunRewPf->addStep(fxeq, ProofRule::REFL, {}, {fx});
            std::vector<Node> cargs;
            ProofRule cr = expr::getCongRule(q[1], cargs);
            Node eqBodyEq = q[1].eqNode(qRew[1]);
            d_defFunRewPf->addStep(eqBodyEq, cr, {fxeq, eqBody}, cargs);
            cargs.clear();
            cr = expr::getCongRule(q, cargs);
            Node eqq = q.eqNode(qRew);
            d_defFunRewPf->addStep(eqq, cr, {eqBodyEq}, cargs);
            d_defFunRewPf->addStep(qRew, ProofRule::EQ_RESOLVE, {q, eqq}, {});
          }
          Node qFinal = nm->mkNode(Kind::FORALL, n[1][0], fx.eqNode(defRew[1]));
          if (qFinal != qRew)
          {
            // The two formulas are equivalent up to renaming the bound
            // variables of closures in the body. We prove this by congruence
            // and alpha-equivalence of the renamed closures, similar to
            // the reconstruction of MACRO_QUANT_ELIM_SHADOW.
            Node eqShadow = qRew.eqNode(qFinal);
            std::vector<Node> matchConds;
            expr::getConversionConditions(qRew, qFinal, matchConds, true);
            TConvProofGenerator tcpg(d_env,
                                     nullptr,
                                     TConvPolicy::ONCE,
                                     TConvCachePolicy::NEVER,
                                     "DefineFunElimShadow",
                                     nullptr,
                                     true);
            for (const Node& mc : matchConds)
            {
              tcpg.addRewriteStep(mc[0],
                                  mc[1],
                                  nullptr,
                                  true,
                                  TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
            }
            std::shared_ptr<ProofNode> pfs = tcpg.getProofForRewriting(qRew);
            if (pfs->getResult() == eqShadow)
            {
              d_defFunRewPf->addProof(pfs);
            }
            else
            {
              Assert(false) << "Failed to eliminate shadowing in " << qRew;
              d_defFunRewPf->addTrustedStep(
                  eqShadow, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
            }
            d_defFunRewPf->addStep(
                qFinal, ProofRule::EQ_RESOLVE, {qRew, eqShadow}, {});
          }
          d_defQuant[n] = q;
          Trace("smt-define-fun") << "...quantified form " << q << std::endl;
          d_assertionListDefs.push_back(n);
          d_env.getTopLevelSubstitutions().addDefinition(
              n[0], defRew, d_defFunRewPf.get(), qFinal, d_defFunRewPf.get());
          return;
        }
      }
      // For definitions that are not lambdas (e.g. define-fun with no
      // arguments), we expand the applications of defined functions in their
      // body, so that applying their substitution in proofs does not
      // introduce applications of defined functions.
      if (isFunDef && d_env.isProofProducing()
          && options().proof.proofDefineFunQuant
          && n[1].getKind() != Kind::LAMBDA)
      {
        TrustNode te = tsm.expandDefinitionsTrusted(defRew);
        if (!te.isNull())
        {
          Assert(defRew == n[1]);
          // ------------------ ASSUME  ------ from tsm
          // c = t                      t = t'
          // --------------------------------- TRANS
          // c = t'
          Node eqExp = te.getProven();
          d_defFunRewPf->addLazyStep(eqExp, te.getGenerator());
          defRew = te.getNode();
          Node eqFinal = n[0].eqNode(defRew);
          d_defFunRewPf->addStep(eqFinal, ProofRule::TRANS, {n, eqExp}, {});
        }
      }
      Trace("smt-define-fun") << "...rewritten to " << defRew << std::endl;
      d_assertionListDefs.push_back(n);
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
