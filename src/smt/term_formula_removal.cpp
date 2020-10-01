/*********************                                                        */
/*! \file term_formula_removal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Removal of term formulas
 **
 ** Removal of term formulas.
 **/
#include "smt/term_formula_removal.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"

using namespace std;

namespace CVC4 {

RemoveTermFormulas::RemoveTermFormulas(context::UserContext* u)
    : d_tfCache(u),
      d_skolem_cache(u),
      d_pnm(nullptr),
      d_tpg(nullptr),
      d_lp(nullptr)
{
}

RemoveTermFormulas::~RemoveTermFormulas() {}

theory::TrustNode RemoveTermFormulas::run(
    Node assertion,
    std::vector<theory::TrustNode>& newAsserts,
    std::vector<Node>& newSkolems,
    bool reportDeps)
{
  Node itesRemoved = runInternal(assertion, newAsserts, newSkolems);
  // In some calling contexts, not necessary to report dependence information.
  if (reportDeps && options::unsatCores())
  {
    // new assertions have a dependence on the node
    if (options::unsatCores())
    {
      ProofManager::currentPM()->addDependence(itesRemoved, assertion);
    }
    unsigned n = 0;
    while (n < newAsserts.size())
    {
      if (options::unsatCores())
      {
        ProofManager::currentPM()->addDependence(newAsserts[n].getProven(),
                                                 assertion);
      }
      ++n;
    }
  }
  // The rewriting of assertion can be justified by the term conversion proof
  // generator d_tpg.
  return theory::TrustNode::mkTrustRewrite(assertion, itesRemoved, d_tpg.get());
}

Node RemoveTermFormulas::runInternal(Node assertion,
                                     std::vector<theory::TrustNode>& output,
                                     std::vector<Node>& newSkolems)
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
      Node currt = runCurrent(curr, output, newSkolems);
      // if null, we need to recurse
      if (!currt.isNull())
      {
        Trace("rtf-debug") << "...replace by skolem" << std::endl;
        d_tfCache.insert(curr, currt);
        ctx.pop();
        processedChildren.pop_back();
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

Node RemoveTermFormulas::runCurrent(std::pair<Node, uint32_t>& curr,
                                    std::vector<theory::TrustNode>& output,
                                    std::vector<Node>& newSkolems)
{
  TNode node = curr.first;
  if (node.getKind() == kind::INST_PATTERN_LIST)
  {
    return Node(node);
  }
  uint32_t cval = curr.second;
  bool inQuant, inTerm;
  RtfTermContext::getFlags(curr.second, inQuant, inTerm);
  Debug("ite") << "removeITEs(" << node << ")"
               << " " << inQuant << " " << inTerm << std::endl;

  NodeManager *nodeManager = NodeManager::currentNM();

  TypeNode nodeType = node.getType();
  Node skolem;
  Node newAssertion;
  // the exists form of the assertion
  ProofGenerator* newAssertionPg = nullptr;
  // Handle non-Boolean ITEs here. Boolean ones (within terms) are handled
  // in the "non-variable Boolean term within term" case below.
  if (node.getKind() == kind::ITE && !nodeType.isBoolean())
  {
    // Here, we eliminate the ITE if we are not Boolean and if we do not contain
    // a free variable.
    if (!inQuant || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        Trace("rtf-proof-debug")
            << "RemoveTermFormulas::run: make ITE skolem" << std::endl;
        // Make the skolem to represent the ITE
        SkolemManager* sm = nodeManager->getSkolemManager();
        skolem = sm->mkPurifySkolem(
            node,
            "termITE",
            "a variable introduced due to term-level ITE removal");
        d_skolem_cache.insert(node, skolem);

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
  }
  else if (node.getKind() == kind::LAMBDA)
  {
    // if a lambda, do lambda-lifting
    if (!inQuant || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        Trace("rtf-proof-debug")
            << "RemoveTermFormulas::run: make LAMBDA skolem" << std::endl;
        // Make the skolem to represent the lambda
        SkolemManager* sm = nodeManager->getSkolemManager();
        skolem = sm->mkPurifySkolem(
            node,
            "lambdaF",
            "a function introduced due to term-level lambda removal");
        d_skolem_cache.insert(node, skolem);

        // The new assertion
        std::vector<Node> children;
        // bound variable list
        children.push_back(node[0]);
        // body
        std::vector<Node> skolem_app_c;
        skolem_app_c.push_back(skolem);
        skolem_app_c.insert(skolem_app_c.end(), node[0].begin(), node[0].end());
        Node skolem_app = nodeManager->mkNode(kind::APPLY_UF, skolem_app_c);
        children.push_back(skolem_app.eqNode(node[1]));
        // axiom defining skolem
        newAssertion = nodeManager->mkNode(kind::FORALL, children);

        // Lambda lifting is trivial to justify, hence we don't set a proof
        // generator here. In particular, replacing the skolem introduced
        // here with its original lambda ensures the new assertion rewrites
        // to true.
        // For example, if (lambda y. t[y]) has skolem k, then this lemma is:
        //   forall x. k(x)=t[x]
        // whose witness form rewrites
        //   forall x. (lambda y. t[y])(x)=t[x] --> forall x. t[x]=t[x] --> true
      }
    }
  }
  else if (node.getKind() == kind::WITNESS)
  {
    // If a witness choice
    //   For details on this operator, see
    //   http://planetmath.org/hilbertsvarepsilonoperator.
    if (!inQuant || !expr::hasFreeVar(node))
    {
      // NOTE: we can replace by t if body is of the form (and (= z t) ...)
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        Trace("rtf-proof-debug")
            << "RemoveTermFormulas::run: make WITNESS skolem" << std::endl;
        // Make the skolem to witness the choice, which notice is handled
        // as a special case within SkolemManager::mkPurifySkolem.
        SkolemManager* sm = nodeManager->getSkolemManager();
        skolem = sm->mkPurifySkolem(
            node,
            "witnessK",
            "a skolem introduced due to term-level witness removal");
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
                            true,
                            "RemoveTermFormulas::run:skolem_pf",
                            false,
                            PfRule::WITNESS_AXIOM);
          d_lp->addStep(newAssertion, PfRule::SKOLEMIZE, {existsAssertion}, {});
          newAssertionPg = d_lp.get();
        }
      }
    }
  }
  else if (node.getKind() != kind::BOOLEAN_TERM_VARIABLE && nodeType.isBoolean()
           && inTerm
           && !inQuant)
  {
    // if a non-variable Boolean term within another term, replace it
    skolem = getSkolemForNode(node);
    if (skolem.isNull())
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make BOOLEAN_TERM_VARIABLE skolem"
          << std::endl;
      // Make the skolem to represent the Boolean term
      // Skolems introduced for Boolean formulas appearing in terms have a
      // special kind (BOOLEAN_TERM_VARIABLE) that ensures they are handled
      // properly in theory combination. We must use this kind here instead of a
      // generic skolem. Notice that the name/comment are currently ignored
      // within SkolemManager::mkPurifySkolem, since BOOLEAN_TERM_VARIABLE
      // variables cannot be given names.
      SkolemManager* sm = nodeManager->getSkolemManager();
      skolem = sm->mkPurifySkolem(
          node,
          "btvK",
          "a Boolean term variable introduced during term formula removal",
          NodeManager::SKOLEM_BOOL_TERM_VAR);
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
      d_tpg->addRewriteStep(node,
                            skolem,
                            PfRule::MACRO_SR_PRED_INTRO,
                            {},
                            {node.eqNode(skolem)},
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

      // Remove ITEs from the new assertion, rewrite it and push it to the
      // output
      Node newAssertionPre = newAssertion;
      newAssertion = runInternal(newAssertion, output, newSkolems);

      if (isProofEnabled())
      {
        if (newAssertionPre != newAssertion)
        {
          Trace("rtf-proof-debug")
              << "RemoveTermFormulas::run: setup proof for processed new lemma"
              << std::endl;
          // for new assertions that rewrite recursively
          Node naEq = newAssertionPre.eqNode(newAssertion);
          d_lp->addLazyStep(naEq, d_tpg.get());
          // ---------------- from lp  ------------------------------- from tpg
          // newAssertionPre            newAssertionPre = newAssertion
          // ------------------------------------------------------- EQ_RESOLVE
          // newAssertion
          d_lp->addStep(
              newAssertion, PfRule::EQ_RESOLVE, {newAssertionPre, naEq}, {});
        }
      }

      theory::TrustNode trna =
          theory::TrustNode::mkTrustLemma(newAssertion, d_lp.get());

      Trace("rtf-proof-debug") << "Checking closed..." << std::endl;
      trna.debugCheckClosed("rtf-proof-debug",
                            "RemoveTermFormulas::run:new_assert");

      output.push_back(trna);
      newSkolems.push_back(skolem);
    }

    // The representation is now the skolem
    return skolem;
  }

  // return null, indicating we will traverse children within runInternal
  return Node::null();
}

Node RemoveTermFormulas::getSkolemForNode(Node node) const
{
  context::CDInsertHashMap<Node, Node, NodeHashFunction>::const_iterator itk =
      d_skolem_cache.find(node);
  if (itk != d_skolem_cache.end())
  {
    return itk->second;
  }
  return Node::null();
}

Node RemoveTermFormulas::replace(TNode node) const
{
  TCtxStack ctx(&d_rtfc);
  ctx.pushInitial(node);
  return replaceInternal(ctx);
}

Node RemoveTermFormulas::replaceInternal(TCtxStack& ctx) const
{
  // get the current node, tagged with a term context identifier
  Assert(!ctx.empty());
  std::pair<Node, uint32_t> curr = ctx.getCurrent();
  ctx.pop();
  TNode node = curr.first;

  if( node.getKind()==kind::INST_PATTERN_LIST ){
    return Node(node);
  }

  // Check the cache
  TermFormulaCache::const_iterator itc = d_tfCache.find(curr);
  if (itc != d_tfCache.end())
  {
    return (*itc).second;
  }

  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Replace in children
  uint32_t cval = curr.second;
  for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; i++)
  {
    ctx.pushChild(node, cval, i);
    Node newChild = replaceInternal(ctx);
    somethingChanged |= (newChild != node[i]);
    newChildren.push_back(newChild);
  }

  // If changes, we rewrite
  if(somethingChanged) {
    return NodeManager::currentNM()->mkNode(node.getKind(), newChildren);
  }
  return node;
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

void RemoveTermFormulas::setProofNodeManager(ProofNodeManager* pnm)
{
  if (d_tpg == nullptr)
  {
    d_pnm = pnm;
    d_tpg.reset(
        new TConvProofGenerator(d_pnm,
                                nullptr,
                                TConvPolicy::FIXPOINT,
                                TConvCachePolicy::NEVER,
                                "RemoveTermFormulas::TConvProofGenerator",
                                &d_rtfc));
    d_lp.reset(new LazyCDProof(
        d_pnm, nullptr, nullptr, "RemoveTermFormulas::LazyCDProof"));
  }
}

bool RemoveTermFormulas::isProofEnabled() const { return d_pnm != nullptr; }

}/* CVC4 namespace */
