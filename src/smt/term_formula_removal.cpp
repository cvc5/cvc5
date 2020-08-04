/*********************                                                        */
/*! \file term_formula_removal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "options/proof_options.h"
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
  TCtxStack ctx(&d_rtfc);
  ctx.pushInitial(assertion);
  Node itesRemoved = run(ctx, newAsserts, newSkolems);
  // In some calling contexts, not necessary to report dependence information.
  if (reportDeps
      && (options::unsatCores() || options::fewerPreprocessingHoles()))
  {
    // new assertions have a dependence on the node
    PROOF(ProofManager::currentPM()->addDependence(itesRemoved, assertion);)
    unsigned n = 0;
    while (n < newAsserts.size())
    {
      PROOF(ProofManager::currentPM()->addDependence(newAsserts[n].getProven(),
                                                     assertion);)
      ++n;
    }
  }
  // The rewriting of assertion can be justified by the term conversion proof
  // generator d_tpg.
  return theory::TrustNode::mkTrustRewrite(assertion, itesRemoved, d_tpg.get());
}

Node RemoveTermFormulas::run(TCtxStack& ctx,
                             std::vector<theory::TrustNode>& output,
                             std::vector<Node>& newSkolems)
{
  // get the current node, tagged with a term context identifier
  Assert (!ctx.empty());
  std::pair<Node, int32_t> curr = ctx.getCurrent();
  ctx.pop();
  TNode node = curr.first;
  Debug("ite") << "removeITEs(" << node << ")" << " " << ctx.inQuant() << " " << ctx.inTerm() << std::endl;

  if( node.getKind()==kind::INST_PATTERN_LIST )
  {
    return Node(node);
  }

  // The result may be cached already
  NodeManager *nodeManager = NodeManager::currentNM();
  TermFormulaCache::const_iterator i = d_tfCache.find(curr);
  if (i != d_tfCache.end())
  {
    Node cached = (*i).second;
    Debug("ite") << "removeITEs: in-cache: " << cached << endl;
    return cached.isNull() ? Node(curr.first) : cached;
  }
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
    if (!ctx.inQuant() || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
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
    if (!ctx.inQuant() || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
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
    if (!ctx.inQuant() || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
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
          if (expg != nullptr)
          {
            d_lp->addLazyStep(existsAssertion, expg);
          }
          d_lp->addStep(newAssertion, PfRule::SKOLEMIZE, {existsAssertion}, {});
          newAssertionPg = d_lp.get();
        }
      }
    }
  }
  else if (node.getKind() != kind::BOOLEAN_TERM_VARIABLE && nodeType.isBoolean()
           && ctx.inTerm()
           && !ctx.inQuant())
  {
    // if a non-variable Boolean term within another term, replace it
    skolem = getSkolemForNode(node);
    if (skolem.isNull())
    {
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
    // Attach the skolem
    d_tfCache.insert(curr, skolem);

    // if the skolem was introduced in this call
    if (!newAssertion.isNull())
    {
      // if proofs are enabled
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
                              {node.eqNode(skolem)});
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
      Debug("ite") << "*** term formula removal introduced " << skolem
                   << " for " << node << std::endl;

      // Remove ITEs from the new assertion, rewrite it and push it to the
      // output
      RtxContext cctx(&d_rtfc);
      cctx.pushInitial(newAssertion);
      newAssertion = run(cctx, output, newSkolems);

      theory::TrustNode trna =
          theory::TrustNode::mkTrustLemma(newAssertion, d_lp.get());

      output.push_back(trna);
      newSkolems.push_back(skolem);
    }

    // The representation is now the skolem
    return skolem;
  }

  // If not an ITE, go deep
  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Remove the ITEs from the children
  int32_t cval = curr.second;
  for (size_t i=0, nchild = node.getNumChildren(); i<nchild; i++)
  {
    ctx.pushChild(node, cval, i);
    Node newChild = run(ctx, output, newSkolems);
    somethingChanged |= (newChild != node[i]);
    newChildren.push_back(newChild);
  }

  // If changes, we rewrite
  if(somethingChanged) {
    Node cached = nodeManager->mkNode(node.getKind(), newChildren);
    d_tfCache.insert(curr, cached);
    return cached;
  } else {
    d_tfCache.insert(curr, Node::null());
    return node;
  }
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


Node RemoveTermFormulas::replace(TNode node) const {
  TCtxStack ctx(&d_rtfc);
  ctx.pushInitial(node);
  replaceInternal(ctx);
}

Node RemoveTermFormulas::replaceInternal(TCtxStack& cxt) const
{  
  // get the current node, tagged with a term context identifier
  Assert (!ctx.empty());
  std::pair<Node, int32_t> curr = ctx.getCurrent();
  ctx.pop();
  TNode node = curr.first;
  
  if( node.getKind()==kind::INST_PATTERN_LIST ){
    return Node(node);
  }

  // Check the cache
  TermFormulaCache::const_iterator i = d_tfCache.find(curr);
  if (i != d_tfCache.end())
  {
    Node cached = (*i).second;
    return cached.isNull() ? Node(node) : cached;
  }

  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Replace in children
  int32_t cval = curr.second;
  for (size_t i=0, nchild = node.getNumChildren(); i<nchild; i++)
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

void RemoveTermFormulas::setProofChecker(ProofChecker* pc)
{
  if (d_tpg == nullptr)
  {
    d_pnm.reset(new ProofNodeManager(pc));
    d_tpg.reset(new TConvProofGenerator(d_pnm.get()));
    d_lp.reset(new LazyCDProof(d_pnm.get()));
  }
}

bool RemoveTermFormulas::isProofEnabled() const { return d_pnm != nullptr; }

}/* CVC4 namespace */
