/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lambda lifting.
 */

#include "theory/uf/lambda_lift.h"

#include "expr/node_algorithm.h"
#include "expr/node_converter.h"
#include "expr/skolem_manager.h"
#include "expr/sort_type_size.h"
#include "options/uf_options.h"
#include "proof/proof.h"
#include "proof/proof_rule_checker.h"
#include "smt/env.h"
#include "theory/uf/function_const.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

/**
 * This node converter is used as a heuristic to avoid certain cases of lambda
 * lifting. For example, (lambda ((x Int)) (f 0)) naively requires lifting
 * since this lambda may have a circular dependency, e.g. if
 * f = (lambda ((x Int)) (f 0)). However, this converter converts this lambda
 * to (lambda ((x Int)) k) where k is the purification skolem for (f 0), where
 * (= k (f 0)) can be added as a lemma at preprocessing.
 */
class PurifyGroundNodeConverter : public NodeConverter
{
 public:
  PurifyGroundNodeConverter(NodeManager* nm) : NodeConverter(nm) {}
  /** post-convert: convert (non-atomic) ground terms to their purify var */
  Node postConvert(Node n) override
  {
    if (!n.isVar() && !n.isConst() && !expr::hasBoundVar(n))
    {
      Node k = SkolemManager::mkPurifySkolem(n);
      d_pterms.push_back(n);
      return k;
    }
    return n;
  }
  /** The list of terms purified by this converter */
  std::vector<Node> d_pterms;
};

LambdaLift::LambdaLift(Env& env)
    : EnvObj(env),
      d_lifted(userContext()),
      d_epg(env.isTheoryProofProducing()
                ? new EagerProofGenerator(env, userContext(), "LambdaLift::epg")
                : nullptr)
{
}

TrustNode LambdaLift::lift(Node node)
{
  if (d_lifted.find(node) != d_lifted.end())
  {
    return TrustNode::null();
  }
  d_lifted.insert(node);
  Node assertion = getAssertionFor(node);
  if (assertion.isNull())
  {
    return TrustNode::null();
  }
  // if no proofs, return lemma with no generator
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustLemma(assertion);
  }
  Node skolem = getSkolemFor(node);
  Assert(!skolem.isNull());
  Node eq = skolem.eqNode(node);
  // --------------- MACRO_SR_PRED_INTRO
  // k = lambda x. t
  // ------------------- MACRO_SR_PRED_INTRO
  // forall x. (k x) = t
  // We do this in two steps, where k -> lambda x. t is used as a subsitution
  // to avoid rare proof checking errors where the conclusion is not
  // provable in one step. In particular, in some rare cases we have that
  // rewrite(toOriginal(rewrite(F))) is not true. For instance, we may end
  // up with (@ (@ f a) b) = (f a b) which does not rewrite to true.
  CDProof cdp(d_env);
  cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
  cdp.addStep(assertion, ProofRule::MACRO_SR_PRED_INTRO, {eq}, {assertion});
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(assertion);
  return d_epg->mkTrustNode(assertion, pf);
}

TrustNode LambdaLift::ppRewrite(Node node, std::vector<SkolemLemma>& lems)
{
  // This method is called on the APPLY_UF, LAMBDA and FUNCTION_ARRAY_CONST
  // terms visited by theory preprocessing (see HoExtension::ppRewrite). The
  // theory preprocessor processes children before their parents, and never
  // descends into the bodies of closures. Hence, when this method is called on
  // an APPLY_UF, its arguments have already been processed by the lambda case
  // below.
  if (node.getKind() == Kind::APPLY_UF)
  {
    if (!options().uf.ufHoLazyLambdaLift)
    {
      // With eager lifting, every closed lambda argument was already replaced
      // by its skolem when the children of node were processed.
      return TrustNode::null();
    }
    // If a lambda that needs lifting occurs as an argument to APPLY_UF, it
    // impacts model construction for the function, and thus must be lifted.
    // For example, if g : Int x Int -> Int, then
    //   (P (lambda ((x Int)) (g x x)))
    // is rewritten to (P k), where k is the purification skolem of the lambda,
    // and the lemmas
    //   (forall ((x Int)) (= (k x) ((lambda ((x Int)) (g x x)) x)))
    //   (= k (lambda ((x Int)) (g x x)))
    // are added. Only the arguments of this application are replaced. The
    // equality connects k to other occurrences of the same lambda, e.g. in
    // (= h (lambda ...)), so that congruence can relate them immediately.
    std::vector<Node> children;
    children.push_back(node.getOperator());
    bool childChanged = false;
    for (const Node& nc : node)
    {
      // nc may be a lambda or a function array constant. The latter never
      // needs lifting, since its body has no free symbols. If nc was purified
      // by the lambda case below, it no longer needs lifting either.
      Node lam = FunctionConst::toLambda(nc);
      Node skolem;
      if (!lam.isNull() && needsLift(lam))
      {
        // This returns the same skolem for every occurrence of lam, and adds
        // its defining lemma once per user context. It returns null if lam
        // has free variables, in which case nc is kept.
        skolem = liftToSkolem(lam, lems);
      }
      childChanged = childChanged || !skolem.isNull();
      children.push_back(skolem.isNull() ? nc : skolem);
    }
    if (!childChanged)
    {
      return TrustNode::null();
    }
    Node ret = nodeManager()->mkNode(Kind::APPLY_UF, children);
    Trace("uf-lazy-ll") << "Lift arguments: " << node << " -> " << ret
                        << std::endl;
    // The preprocessor revisits ret. Its arguments that were lambdas are now
    // skolems, so no further rewrite applies.
    return mkTrustedRewrite(node, ret);
  }
  // Otherwise, node is a lambda or a function array constant, and lam is its
  // lambda form. Any other node is not rewritten.
  Node lam = FunctionConst::toLambda(node);
  if (lam.isNull())
  {
    return TrustNode::null();
  }
  if (options().uf.ufHoLazyLambdaLift)
  {
    // We do not lift lambdas here. Lambdas that need lifting are lifted only
    // when they impact model construction, that is, when they occur as
    // arguments to APPLY_UF (see above), or are equated to ordinary functions
    // (see HoExtension::checkLazyLambda).
    //
    // A lambda that does not need lifting stays in the term. Its applications
    // are beta-reduced by the rewriter, and it can be used directly as the
    // model value of its equivalence class.
    if (!needsLift(lam))
    {
      return TrustNode::null();
    }
    // Maybe it would help to purify the ground subterms? If so we rewrite
    // and add purification lemmas to lems.
    PurifyGroundNodeConverter pgnc(nodeManager());
    Node clam = pgnc.convert(lam);
    // If purification does not help, the lambda also stays in the term. It is
    // lifted later if it occurs as an argument to APPLY_UF (see above), or if
    // it is equated to an ordinary function (see
    // HoExtension::checkLazyLambda).
    if (needsLift(clam))
    {
      return TrustNode::null();
    }
    Trace("uf-lazy-ll-purify") << "ppRewrite " << lam << " to " << clam
                               << " to avoid lifting." << std::endl;
    // add purification lemmas for terms we purified
    for (const Node& t : pgnc.d_pterms)
    {
      Node k = SkolemManager::mkPurifySkolem(t);
      TrustNode trnk = TrustNode::mkTrustLemma(k.eqNode(t));
      Trace("uf-lazy-ll-purify")
          << "- purify lemma: " << k.eqNode(t) << std::endl;
      lems.push_back(SkolemLemma(trnk, k));
    }
    // We return the purified lambda itself, not a skolem for it. The
    // preprocessor revisits clam, which does not need lifting, so no further
    // rewrite applies. Note that this rewrite has no proof generator.
    return TrustNode::mkTrustRewrite(node, clam);
  }
  // Otherwise, we lift all lambdas eagerly (--no-uf-lazy-ll): node is replaced
  // by its skolem, and the lemma defining the skolem is added.
  Node skolem = liftToSkolem(lam, lems);
  if (skolem.isNull())
  {
    return TrustNode::null();
  }
  return mkTrustedRewrite(node, skolem);
}

Node LambdaLift::liftToSkolem(const Node& lam, std::vector<SkolemLemma>& lems)
{
  Node skolem = getSkolemFor(lam);
  if (skolem.isNull())
  {
    return skolem;
  }
  TrustNode trn = lift(lam);
  if (!trn.isNull())
  {
    lems.push_back(SkolemLemma(trn, skolem));
    if (options().uf.ufHoLazyLambdaLift)
    {
      // Other occurrences of lam may remain inline. Connect them to skolem
      // once per user context, together with its defining lemma.
      Node eq = skolem.eqNode(lam);
      TrustNode teq = d_epg == nullptr
                          ? TrustNode::mkTrustLemma(eq)
                          : d_epg->mkTrustNode(
                                eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
      lems.push_back(SkolemLemma(teq, skolem));
    }
  }
  return skolem;
}

TrustNode LambdaLift::mkTrustedRewrite(const Node& n, const Node& ret) const
{
  // if no proofs, return rewrite with no generator
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustRewrite(n, ret);
  }
  // The rewrite is justified by replacing the purification skolems in ret by
  // the lambdas they purify.
  return d_epg->mkTrustedRewrite(
      n, ret, ProofRule::MACRO_SR_PRED_INTRO, {n.eqNode(ret)});
}

bool LambdaLift::needsLift(const Node& lam)
{
  Assert(lam.getKind() == Kind::LAMBDA);
  std::map<Node, bool>::iterator it = d_needsLift.find(lam);
  if (it != d_needsLift.end())
  {
    return it->second;
  }
  // Model construction considers types in order of their type size
  // (SortTypeSize::getTypeSize). If the lambda has a free variable, that
  // comes later in the model construction, it may need to be lifted eagerly.
  // As an example, say f : Int -> Int, g : Int x Int -> Int
  // The following lambdas require eager lifting:
  // - (lambda ((x Int)) (g x x))
  // - (lambda ((x Int) (y Int)) (f (g x y)))
  // The following lambdas do not require eager lifting:
  // - (lambda ((x Int)) (+ x 1)), since it has no free symbols.
  // - (lambda ((x Int) (y Int)) (f x)), since its free symbol f has a type
  // Int -> Int which is processed before the type of the lambda, i.e.
  // Int x Int -> Int.
  bool shouldLift = false;
  std::unordered_set<Node> syms;
  expr::getSymbols(lam[1], syms);
  SortTypeSize sts;
  size_t lsize = sts.getTypeSize(lam.getType());
  Trace("uf-lazy-ll") << "Lift " << lam << "?" << std::endl;
  for (const Node& v : syms)
  {
    TypeNode tn = v.getType();
    if (!tn.isFirstClass())
    {
      // don't need to worry about constructor/selector/testers/etc.
      continue;
    }
    size_t vsize = sts.getTypeSize(tn);
    if (vsize >= lsize)
    {
      shouldLift = true;
      Trace("uf-lazy-ll") << "...yes due to " << v << std::endl;
      break;
    }
  }
  d_needsLift[lam] = shouldLift;
  return shouldLift;
}

TrustNode LambdaLift::getLiftLemma(const Node& f, const Node& n) const
{
  // Unlike the lemma of lift, which defines a fresh skolem, this lemma is
  // stated for a term f that already has a meaning, and hence it must be
  // conditioned on (= f n). It is valid by congruence. Note that f is any
  // ordinary function in the equivalence class of n, and need not be a
  // variable, e.g. it may be a partial application (@ g t), in which case the
  // rewriter turns (f x) into a full application of g.
  Node lam = getLambdaFor(n);
  Assert(!lam.isNull());
  NodeManager* nm = nodeManager();
  std::vector<Node> fapp;
  std::vector<Node> lapp;
  fapp.push_back(f);
  lapp.push_back(n);
  // We use the bound variables of lam as the variables of the quantified
  // formula, as in getAssertionFor.
  fapp.insert(fapp.end(), lam[0].begin(), lam[0].end());
  lapp.insert(lapp.end(), lam[0].begin(), lam[0].end());
  // We use (n x) instead of the body of lam as the right hand side, since
  // beta reduction uses capture-avoiding substitution. Function array
  // constants are converted to lambdas by rewriting.
  Node eq =
      nm->mkNode(Kind::APPLY_UF, fapp).eqNode(nm->mkNode(Kind::APPLY_UF, lapp));
  Node univ = nm->mkNode(Kind::FORALL, lam[0], eq);
  Node premise = f.eqNode(n);
  Node lem = nm->mkNode(Kind::IMPLIES, premise, univ);
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustLemma(lem);
  }
  // Prove the pointwise equality by congruence, then lift its equality to
  // true under the quantifier and discharge the premise. Substituting f -> n
  // throughout univ would also change occurrences of f inside n, so it would
  // not reduce univ to true for circular lambdas such as
  // n = (lambda ((x Int)) (+ 1 (f x))).
  CDProof cdp(d_env);
  std::vector<Node> premises{premise};
  for (const Node& v : lam[0])
  {
    Node refl = v.eqNode(v);
    cdp.addStep(refl, ProofRule::REFL, {}, {v});
    premises.push_back(refl);
  }
  cdp.addStep(eq,
              ProofRule::HO_CONG,
              premises,
              {ProofRuleChecker::mkKindNode(nm, Kind::APPLY_UF)});
  Node eqTrue = eq.eqNode(nm->mkConst(true));
  cdp.addStep(eqTrue, ProofRule::TRUE_INTRO, {eq}, {});
  Node univTrue = nm->mkNode(Kind::FORALL, lam[0], nm->mkConst(true));
  Node univEq = univ.eqNode(univTrue);
  cdp.addStep(univEq, ProofRule::CONG, {eqTrue}, {univ});
  cdp.addStep(univ, ProofRule::MACRO_SR_PRED_INTRO, {univEq}, {univ});
  cdp.addStep(lem, ProofRule::SCOPE, {univ}, {premise});
  return d_epg->mkTrustNode(lem, cdp.getProofFor(lem));
}

Node LambdaLift::getLambdaFor(TNode n) { return FunctionConst::toLambda(n); }

bool LambdaLift::isLambda(TNode n)
{
  Kind k = n.getKind();
  return k == Kind::LAMBDA || k == Kind::FUNCTION_ARRAY_CONST;
}

Node LambdaLift::getAssertionFor(TNode node)
{
  Node assertion;
  Node lambda = FunctionConst::toLambda(node);
  if (!lambda.isNull())
  {
    TNode skolem = getSkolemFor(node);
    Assert(!skolem.isNull());
    NodeManager* nm = node.getNodeManager();
    // The new assertion
    std::vector<Node> children;
    // bound variable list
    children.push_back(lambda[0]);
    // body
    std::vector<Node> skolem_app_c;
    skolem_app_c.push_back(skolem);
    skolem_app_c.insert(skolem_app_c.end(), lambda[0].begin(), lambda[0].end());
    Node skolem_app = nm->mkNode(Kind::APPLY_UF, skolem_app_c);
    skolem_app_c[0] = lambda;
    Node rhs = nm->mkNode(Kind::APPLY_UF, skolem_app_c);
    // For the sake of proofs, we use
    // (= (k t1 ... tn) ((lambda (x1 ... xn) s) t1 ... tn)) here. This is
    // instead of
    // (= (k t1 ... tn) s); the former is more accurate since
    // beta reduction uses capture-avoiding substitution, which implies that
    // ((lambda (y1 ... yn) s) t1 ... tn) is alpha-equivalent but not
    // necessarily syntactical equal to s.
    children.push_back(skolem_app.eqNode(rhs));
    // axiom defining skolem
    assertion = nm->mkNode(Kind::FORALL, children);

    // Lambda lifting is trivial to justify, hence we don't set a proof
    // generator here. In particular, replacing the skolem introduced
    // here with its original lambda ensures the new assertion rewrites
    // to true.
    // For example, if (lambda y. t[y]) has skolem k, then this lemma is:
    //   forall x. k(x)=t[x]
    // whose witness form rewrites
    //   forall x. (lambda y. t[y])(x)=t[x] --> forall x. t[x]=t[x] --> true
  }
  return assertion;
}

Node LambdaLift::getSkolemFor(TNode node)
{
  Node skolem;
  Node lambda = FunctionConst::toLambda(node);
  if (!lambda.isNull())
  {
    // if a lambda, return the purification variable for the node. We ignore
    // lambdas with free variables, which can occur beneath quantifiers
    // during preprocessing.
    if (!expr::hasFreeVar(node))
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make LAMBDA skolem" << std::endl;
      // Make the skolem to represent the lambda
      skolem = SkolemManager::mkPurifySkolem(node);
    }
  }
  return skolem;
}

Node LambdaLift::betaReduce(TNode lam, const std::vector<Node>& args) const
{
  Assert(lam.getKind() == Kind::LAMBDA);
  std::vector<Node> betaRed;
  betaRed.push_back(lam);
  betaRed.insert(betaRed.end(), args.begin(), args.end());
  Node app = nodeManager()->mkNode(Kind::APPLY_UF, betaRed);
  app = rewrite(app);
  return app;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
