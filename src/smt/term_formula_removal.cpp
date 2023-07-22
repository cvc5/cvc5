/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Removal of term formulas.
 */
#include "smt/term_formula_removal.h"

#include <vector>

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/term_context_stack.h"
#include "options/smt_options.h"
#include "proof/conv_proof_generator.h"
#include "proof/lazy_proof.h"
#include "smt/env.h"
#include "smt/logic_exception.h"

using namespace std;

namespace cvc5::internal {

RemoveTermFormulas::RemoveTermFormulas(Env& env)
    : EnvObj(env),
      d_tfCache(userContext()),
      d_skolem_cache(userContext()),
      d_tpg(nullptr),
      d_lp(nullptr)
{
  // enable proofs if necessary
  ProofNodeManager* pnm = env.getProofNodeManager();
  if (pnm != nullptr)
  {
    d_tpg.reset(
        new TConvProofGenerator(env,
                                nullptr,
                                TConvPolicy::FIXPOINT,
                                TConvCachePolicy::NEVER,
                                "RemoveTermFormulas::TConvProofGenerator",
                                &d_rtfc));
    d_tpgi.reset(
        new TConvProofGenerator(env,
                                nullptr,
                                TConvPolicy::ONCE,
                                TConvCachePolicy::NEVER,
                                "RemoveTermFormulas::TConvProofGenerator"));
    d_lp.reset(new LazyCDProof(
        env, nullptr, nullptr, "RemoveTermFormulas::LazyCDProof"));
  }
}

RemoveTermFormulas::~RemoveTermFormulas() {}

TrustNode RemoveTermFormulas::run(TNode assertion,
                                  std::vector<theory::SkolemLemma>& newAsserts,
                                  bool fixedPoint)
{
  Node itesRemoved = runInternal(assertion, newAsserts);
  if (itesRemoved == assertion)
  {
    return TrustNode::null();
  }
  // if running to fixed point, we run each new assertion through the
  // run lemma method
  if (fixedPoint)
  {
    size_t i = 0;
    while (i < newAsserts.size())
    {
      TrustNode trn = newAsserts[i].d_lemma;
      // do not run to fixed point on subcall, since we are processing all
      // lemmas in this loop
      newAsserts[i].d_lemma = runLemma(trn, newAsserts, false);
      i++;
    }
  }
  // The rewriting of assertion can be justified by the term conversion proof
  // generator d_tpg.
  return TrustNode::mkTrustRewrite(assertion, itesRemoved, d_tpg.get());
}

TrustNode RemoveTermFormulas::runLemma(
    TrustNode lem,
    std::vector<theory::SkolemLemma>& newAsserts,
    bool fixedPoint)
{
  TrustNode trn = run(lem.getProven(), newAsserts, fixedPoint);
  if (trn.isNull())
  {
    // no change
    return lem;
  }
  Assert(trn.getKind() == TrustNodeKind::REWRITE);
  Node newAssertion = trn.getNode();
  if (!d_env.isTheoryProofProducing())
  {
    // proofs not enabled, just take result
    return TrustNode::mkTrustLemma(newAssertion, nullptr);
  }
  Trace("rtf-proof-debug")
      << "RemoveTermFormulas::run: setup proof for processed new lemma"
      << std::endl;
  Node assertionPre = lem.getProven();
  Node naEq = trn.getProven();
  // this method is applying this method to TrustNode whose generator is
  // already d_lp (from the run method above), in which case this link is
  // not necessary.
  if (trn.getGenerator() != d_lp.get())
  {
    d_lp->addLazyStep(naEq, trn.getGenerator());
  }
  // ---------------- from input  ------------------------------- from trn
  // assertionPre                 assertionPre = newAssertion
  // ------------------------------------------------------- EQ_RESOLVE
  // newAssertion
  d_lp->addStep(newAssertion, PfRule::EQ_RESOLVE, {assertionPre, naEq}, {});
  return TrustNode::mkTrustLemma(newAssertion, d_lp.get());
}

Node RemoveTermFormulas::runInternal(TNode assertion,
                                     std::vector<theory::SkolemLemma>& output)
{
  NodeManager* nm = NodeManager::currentNM();
  TCtxStack ctx(&d_rtfc);
  std::vector<bool> processedChildren;
  ctx.pushInitial(assertion);
  processedChildren.push_back(false);
  std::pair<Node, uint32_t> initial = ctx.getCurrent();
  std::pair<Node, uint32_t> curr;
  Node node;
  uint32_t nodeVal;
  TermFormulaCache::const_iterator itc;
  while (!ctx.empty())
  {
    curr = ctx.getCurrent();
    itc = d_tfCache.find(curr);
    node = curr.first;
    nodeVal = curr.second;
    Trace("rtf-debug") << "Visit " << node << ", " << nodeVal << std::endl;
    if (itc != d_tfCache.end())
    {
      Trace("rtf-debug") << "...already computed" << std::endl;
      ctx.pop();
      processedChildren.pop_back();
      // already computed
      continue;
    }
    // if we have yet to process children
    if (!processedChildren.back())
    {
      // check if we should replace the current node
      TrustNode newLem;
      bool inQuant, inTerm;
      RtfTermContext::getFlags(nodeVal, inQuant, inTerm);
      Trace("ite") << "removeITEs(" << node << ")"
                   << " " << inQuant << " " << inTerm << std::endl;
      Assert(!inQuant);
      Node currt =
          runCurrentInternal(node, inTerm, newLem, nodeVal, d_tpg.get());
      // if we replaced by a skolem, we do not recurse
      if (!currt.isNull())
      {
        // if this is the first time we've seen this term, we have a new lemma
        // which we add to our vectors
        if (!newLem.isNull())
        {
          output.push_back(theory::SkolemLemma(newLem, currt));
        }
        Trace("rtf-debug") << "...replace by skolem" << std::endl;
        d_tfCache.insert(curr, currt);
        ctx.pop();
        processedChildren.pop_back();
      }
      else if (node.isClosure())
      {
        // currently, we never do any term formula removal in quantifier bodies
        d_tfCache.insert(curr, node);
      }
      else
      {
        size_t nchild = node.getNumChildren();
        if (nchild > 0)
        {
          Trace("rtf-debug") << "...recurse to children" << std::endl;
          // recurse if we have children
          processedChildren[processedChildren.size() - 1] = true;
          for (size_t i = 0; i < nchild; i++)
          {
            ctx.pushChild(node, nodeVal, i);
            processedChildren.push_back(false);
          }
        }
        else
        {
          Trace("rtf-debug") << "...base case" << std::endl;
          d_tfCache.insert(curr, node);
          ctx.pop();
          processedChildren.pop_back();
        }
      }
      continue;
    }
    Trace("rtf-debug") << "...reconstruct" << std::endl;
    // otherwise, we are now finished processing children, pop the current node
    // and compute the result
    ctx.pop();
    processedChildren.pop_back();
    // if we have not already computed the result
    std::vector<Node> newChildren;
    bool childChanged = false;
    if (node.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      newChildren.push_back(node.getOperator());
    }
    // reconstruct from the children
    std::pair<Node, uint32_t> currChild;
    for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; i++)
    {
      // recompute the value of the child
      uint32_t val = d_rtfc.computeValue(node, nodeVal, i);
      currChild = std::pair<Node, uint32_t>(node[i], val);
      itc = d_tfCache.find(currChild);
      Assert(itc != d_tfCache.end());
      Node newChild = (*itc).second;
      Assert(!newChild.isNull());
      childChanged |= (newChild != node[i]);
      newChildren.push_back(newChild);
    }
    // If changes, we reconstruct the node
    Node ret = node;
    if (childChanged)
    {
      ret = nm->mkNode(node.getKind(), newChildren);
    }
    // cache
    d_tfCache.insert(curr, ret);
  }
  itc = d_tfCache.find(initial);
  Assert(itc != d_tfCache.end());
  return (*itc).second;
}

TrustNode RemoveTermFormulas::runCurrent(TNode node,
                                         bool inTerm,
                                         TrustNode& newLem)
{
  // use the term conversion generator that is term context insensitive, with
  // cval set to 0.
  Node k = runCurrentInternal(node, inTerm, newLem, 0, d_tpgi.get());
  if (!k.isNull())
  {
    return TrustNode::mkTrustRewrite(node, k, d_tpgi.get());
  }
  return TrustNode::null();
}

Node RemoveTermFormulas::runCurrentInternal(TNode node,
                                            bool inTerm,
                                            TrustNode& newLem,
                                            uint32_t cval,
                                            TConvProofGenerator* pg)
{
  NodeManager *nodeManager = NodeManager::currentNM();
  SkolemManager* sm = nodeManager->getSkolemManager();

  TypeNode nodeType = node.getType();
  Node skolem;
  Node newAssertion;
  // the exists form of the assertion
  ProofGenerator* newAssertionPg = nullptr;
  // Handle non-Boolean ITEs here. Boolean ones (within terms) are handled
  // in the "non-variable Boolean term within term" case below.
  if (node.getKind() == kind::ITE && !nodeType.isBoolean())
  {
    if (!nodeType.isFirstClass())
    {
      std::stringstream ss;
      ss << "ITE branches of type " << nodeType
         << " are currently not supported." << std::endl;
      throw LogicException(ss.str());
    }
    // Here, we eliminate the ITE if we are not Boolean and if we are
    // not in a quantified formula. This policy should be in sync with
    // the policy for when to apply theory preprocessing to terms, see PR
    // #5497.
    skolem = getSkolemForNode(node);
    if (skolem.isNull())
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make ITE skolem" << std::endl;
      // Make the skolem to represent the ITE
      skolem = sm->mkPurifySkolem(node);
      d_skolem_cache.insert(node, skolem);

      // Notice that in very rare cases, two different terms may have the
      // same purification skolem (see SkolemManager::mkPurifySkolem) For such
      // cases, for simplicity, we repeat the work of constructing the
      // assertion and proofs below. This is so that the proof for the new form
      // of the lemma is used.

      // The new assertion
      newAssertion = nodeManager->mkNode(
          kind::ITE, node[0], skolem.eqNode(node[1]), skolem.eqNode(node[2]));

      // we justify it internally
      if (isProofEnabled())
      {
        Trace("rtf-proof-debug")
            << "RemoveTermFormulas::run: justify " << newAssertion
            << " with ITE axiom" << std::endl;
        // ---------------------- REMOVE_TERM_FORMULA_AXIOM
        // (ite node[0]
        //      (= node node[1])            ------------- MACRO_SR_PRED_INTRO
        //      (= node node[2]))           node = skolem
        // ------------------------------------------ MACRO_SR_PRED_TRANSFORM
        // (ite node[0] (= skolem node[1]) (= skolem node[2]))
        //
        // Note that the MACRO_SR_PRED_INTRO step holds due to conversion
        // of skolem into its witness form, which is node.
        Node axiom = getAxiomFor(node);
        d_lp->addStep(axiom, PfRule::REMOVE_TERM_FORMULA_AXIOM, {}, {node});
        Node eq = node.eqNode(skolem);
        d_lp->addStep(eq, PfRule::MACRO_SR_PRED_INTRO, {}, {eq});
        d_lp->addStep(newAssertion,
                      PfRule::MACRO_SR_PRED_TRANSFORM,
                      {axiom, eq},
                      {newAssertion});
        newAssertionPg = d_lp.get();
      }
    }
  }
  else if (node.getKind() == kind::WITNESS)
  {
    // If a witness choice
    //   For details on this operator, see
    //   http://planetmath.org/hilbertsvarepsilonoperator.
    if (!expr::hasFreeVar(node))
    {
      // NOTE: we can replace by t if body is of the form (and (= z t) ...)
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        Trace("rtf-proof-debug")
            << "RemoveTermFormulas::run: make WITNESS skolem" << std::endl;
        // Make the skolem to witness the choice, which notice is handled
        // as a special case within SkolemManager::mkPurifySkolem.
        skolem = sm->mkPurifySkolem(node);
        d_skolem_cache.insert(node, skolem);

        Assert(node[0].getNumChildren() == 1);

        // The new assertion is the assumption that the body
        // of the witness operator holds for the Skolem
        newAssertion = node[1].substitute(node[0][0], skolem);

        // Get the proof generator, if one exists, which was responsible for
        // constructing this witness term. This may not exist, in which case
        // the witness term was trivial to justify. This is the case e.g. for
        // purification witness terms.
        if (isProofEnabled())
        {
          Node existsAssertion =
              nodeManager->mkNode(kind::EXISTS, node[0], node[1]);
          // -------------------- from skolem manager
          // (exists x. node[1])
          // -------------------- SKOLEMIZE
          // node[1] * { x -> skolem }
          ProofGenerator* expg = sm->getProofGenerator(existsAssertion);
          d_lp->addLazyStep(existsAssertion,
                            expg,
                            PfRule::WITNESS_AXIOM,
                            true,
                            "RemoveTermFormulas::run:skolem_pf");
          d_lp->addStep(newAssertion, PfRule::SKOLEMIZE, {existsAssertion}, {});
          newAssertionPg = d_lp.get();
        }
      }
    }
  }
  else if (nodeType.isBoolean() && inTerm
           && sm->getId(node) != SkolemFunId::PURIFY)
  {
    // if a non-variable Boolean term within another term, replace it
    skolem = getSkolemForNode(node);
    if (skolem.isNull())
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make Boolean skolem" << std::endl;
      // Make the skolem to represent the Boolean term
      // Skolems introduced for Boolean formulas appearing in terms are
      // purified here (SkolemFunId::PURIFY), which ensures they are handled
      // properly in theory combination.
      skolem = sm->mkPurifySkolem(node);
      d_skolem_cache.insert(node, skolem);

      // The new assertion
      newAssertion = skolem.eqNode(node);

      // Boolean term removal is trivial to justify, hence we don't set a proof
      // generator here. It is trivial to justify since it is an instance of
      // purification, which is justified by conversion to witness forms.
    }
  }

  // if the term should be replaced by a skolem
  if( !skolem.isNull() ){
    // this must be done regardless of whether the assertion was new below,
    // since a formula-term may rewrite to the same skolem in multiple contexts.
    if (isProofEnabled())
    {
      // justify the introduction of the skolem
      // ------------------- MACRO_SR_PRED_INTRO
      // t = witness x. x=t
      // The above step is trivial, since the skolems introduced above are
      // all purification skolems. We record this equality in the term
      // conversion proof generator.
      pg->addRewriteStep(node,
                         skolem,
                         PfRule::MACRO_SR_PRED_INTRO,
                         {},
                         {node.eqNode(skolem)},
                         true,
                         cval);
    }

    // if the skolem was introduced in this call
    if (!newAssertion.isNull())
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: setup proof for new assertion "
          << newAssertion << std::endl;
      // if proofs are enabled
      if (isProofEnabled())
      {
        // justify the axiom that defines the skolem, if not already done so
        if (newAssertionPg == nullptr)
        {
          // Should have trivial justification if not yet provided. This is the
          // case of lambda lifting and Boolean term removal.
          // ---------------- MACRO_SR_PRED_INTRO
          // newAssertion
          d_lp->addStep(
              newAssertion, PfRule::MACRO_SR_PRED_INTRO, {}, {newAssertion});
        }
      }
      Trace("rtf-debug") << "*** term formula removal introduced " << skolem
                         << " for " << node << std::endl;

      newLem = TrustNode::mkTrustLemma(newAssertion, d_lp.get());

      Trace("rtf-proof-debug") << "Checking closed..." << std::endl;
      newLem.debugCheckClosed(
          options(), "rtf-proof-debug", "RemoveTermFormulas::run:new_assert");
    }

    // The representation is now the skolem
    return skolem;
  }

  // return null, indicating we will traverse children within runInternal
  return Node::null();
}

Node RemoveTermFormulas::getSkolemForNode(Node k) const
{
  context::CDInsertHashMap<Node, Node>::const_iterator itk =
      d_skolem_cache.find(k);
  if (itk != d_skolem_cache.end())
  {
    return itk->second;
  }
  return Node::null();
}

Node RemoveTermFormulas::getAxiomFor(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  if (k == kind::ITE)
  {
    return nm->mkNode(kind::ITE, n[0], n.eqNode(n[1]), n.eqNode(n[2]));
  }
  return Node::null();
}

ProofGenerator* RemoveTermFormulas::getTConvProofGenerator()
{
  return d_tpg.get();
}

bool RemoveTermFormulas::isProofEnabled() const { return d_tpg != nullptr; }

}  // namespace cvc5::internal
