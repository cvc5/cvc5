/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for processing proof nodes.
 */

#include "smt/proof_post_processor.h"

#include "expr/skolem_manager.h"
#include "options/proof_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/resolution_proofs_util.h"
#include "theory/arith/arith_utilities.h"
#include "theory/builtin/proof_checker.h"
#include "theory/bv/bitblast/bitblast_proof_generator.h"
#include "theory/bv/bitblast/proof_bitblaster.h"
#include "theory/rewriter.h"
#include "theory/strings/infer_proof_cons.h"
#include "theory/theory.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ProofPostprocessCallback::ProofPostprocessCallback(Env& env,
                                                   rewriter::RewriteDb* rdb,
                                                   bool updateScopedAssumptions)
    : EnvObj(env),
      d_pc(nullptr),
      d_pppg(nullptr),
      d_rdbPc(env, rdb),
      d_wfpm(env),
      d_elimAllTrusted(false),
      d_updateScopedAssumptions(updateScopedAssumptions)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

void ProofPostprocessCallback::initializeUpdate(ProofGenerator* pppg)
{
  d_pppg = pppg;
  d_assumpToProof.clear();
  d_wfAssumptions.clear();
  d_pc = d_env.getProofNodeManager()->getChecker();
}

void ProofPostprocessCallback::setEliminateRule(PfRule rule)
{
  d_elimRules.insert(rule);
}

void ProofPostprocessCallback::setEliminateAllTrustedRules()
{
  d_elimAllTrusted = true;
}

bool ProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                            const std::vector<Node>& fa,
                                            bool& continueUpdate)
{
  PfRule id = pn->getRule();
  if (shouldExpand(id))
  {
    return true;
  }
  // other than elimination rules, we always update assumptions as long as
  // d_updateScopedAssumptions is true or they are *not* in scope, i.e., not in
  // fa
  if (id != PfRule::ASSUME)
  {
    return false;
  }
  if (!d_updateScopedAssumptions
      && std::find(fa.begin(), fa.end(), pn->getResult()) != fa.end())
  {
    Trace("smt-proof-pp-debug")
        << "... not updating in-scope assumption " << pn->getResult() << "\n";
    return false;
  }
  return true;
}

bool ProofPostprocessCallback::update(Node res,
                                      PfRule id,
                                      const std::vector<Node>& children,
                                      const std::vector<Node>& args,
                                      CDProof* cdp,
                                      bool& continueUpdate)
{
  Trace("smt-proof-pp-debug") << "- Post process " << id << " " << children
                              << " / " << args << std::endl;

  if (id == PfRule::ASSUME)
  {
    // we cache based on the assumption node, not the proof node, since there
    // may be multiple occurrences of the same node.
    Node f = args[0];
    std::shared_ptr<ProofNode> pfn;
    std::map<Node, std::shared_ptr<ProofNode>>::iterator it =
        d_assumpToProof.find(f);
    if (it != d_assumpToProof.end())
    {
      Trace("smt-proof-pp-debug") << "...already computed" << std::endl;
      pfn = it->second;
    }
    else
    {
      Trace("smt-proof-pp-debug") << "...get proof" << std::endl;
      Assert(d_pppg != nullptr);
      // get proof from preprocess proof generator
      pfn = d_pppg->getProofFor(f);
      Trace("smt-proof-pp-debug") << "...finished get proof" << std::endl;
      // print for debugging
      if (pfn == nullptr)
      {
        Trace("smt-proof-pp-debug")
            << "...no proof, possibly an input assumption" << std::endl;
      }
      else
      {
        Assert(pfn->getResult() == f);
        if (TraceIsOn("smt-proof-pp"))
        {
          Trace("smt-proof-pp")
              << "=== Connect proof for preprocessing: " << f << std::endl;
          Trace("smt-proof-pp") << *pfn.get() << std::endl;
        }
      }
      d_assumpToProof[f] = pfn;
    }
    if (pfn == nullptr || pfn->getRule() == PfRule::ASSUME)
    {
      Trace("smt-proof-pp-debug") << "...do not add proof" << std::endl;
      // no update
      return false;
    }
    Trace("smt-proof-pp-debug") << "...add proof" << std::endl;
    // connect the proof
    cdp->addProof(pfn);
    return true;
  }
  Node ret = expandMacros(id, children, args, cdp, res);
  Trace("smt-proof-pp-debug") << "...expanded = " << !ret.isNull() << std::endl;
  return !ret.isNull();
}

bool ProofPostprocessCallback::updateInternal(Node res,
                                              PfRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args,
                                              CDProof* cdp)
{
  bool continueUpdate = true;
  return update(res, id, children, args, cdp, continueUpdate);
}

bool ProofPostprocessCallback::shouldExpand(PfRule id) const
{
  if (d_elimRules.find(id) != d_elimRules.end())
  {
    return true;
  }
  if (d_elimAllTrusted && d_pc->getPedanticLevel(id) > 0)
  {
    return true;
  }
  return false;
}

Node ProofPostprocessCallback::expandMacros(PfRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args,
                                            CDProof* cdp,
                                            Node res)
{
  if (!shouldExpand(id))
  {
    // not eliminated
    return Node::null();
  }
  Trace("smt-proof-pp-debug") << "Expand macro " << id << std::endl;
  // macro elimination
  if (id == PfRule::MACRO_SR_EQ_INTRO)
  {
    // (TRANS
    //   (SUBS <children> :args args[0:1])
    //   (REWRITE :args <t.substitute(x1,t1). ... .substitute(xn,tn)> args[2]))
    std::vector<Node> tchildren;
    Node t = args[0];
    Node ts;
    if (!children.empty())
    {
      std::vector<Node> sargs;
      sargs.push_back(t);
      MethodId ids = MethodId::SB_DEFAULT;
      if (args.size() >= 2)
      {
        if (getMethodId(args[1], ids))
        {
          sargs.push_back(args[1]);
        }
      }
      MethodId ida = MethodId::SBA_SEQUENTIAL;
      if (args.size() >= 3)
      {
        if (getMethodId(args[2], ida))
        {
          sargs.push_back(args[2]);
        }
      }
      ts = builtin::BuiltinProofRuleChecker::applySubstitution(
          t, children, ids, ida);
      Trace("smt-proof-pp-debug")
          << "...eq intro subs equality is " << t << " == " << ts << ", from "
          << ids << " " << ida << std::endl;
      if (ts != t)
      {
        Node eq = t.eqNode(ts);
        // apply SUBS proof rule if necessary
        if (!updateInternal(eq, PfRule::SUBS, children, sargs, cdp))
        {
          // if we specified that we did not want to eliminate, add as step
          cdp->addStep(eq, PfRule::SUBS, children, sargs);
        }
        tchildren.push_back(eq);
      }
    }
    else
    {
      // no substitute
      ts = t;
    }
    std::vector<Node> rargs;
    rargs.push_back(ts);
    MethodId idr = MethodId::RW_REWRITE;
    if (args.size() >= 4)
    {
      if (getMethodId(args[3], idr))
      {
        rargs.push_back(args[3]);
      }
    }
    Node tr = d_env.rewriteViaMethod(ts, idr);
    Trace("smt-proof-pp-debug")
        << "...eq intro rewrite equality is " << ts << " == " << tr << ", from "
        << idr << std::endl;
    if (ts != tr)
    {
      Node eq = ts.eqNode(tr);
      // apply REWRITE proof rule
      if (!updateInternal(eq, PfRule::REWRITE, {}, rargs, cdp))
      {
        // if not elimianted, add as step
        cdp->addStep(eq, PfRule::REWRITE, {}, rargs);
      }
      tchildren.push_back(eq);
    }
    if (t == tr)
    {
      // typically not necessary, but done to be robust
      cdp->addStep(t.eqNode(tr), PfRule::REFL, {}, {t});
      return t.eqNode(tr);
    }
    // must add TRANS if two step
    return addProofForTrans(tchildren, cdp);
  }
  else if (id == PfRule::MACRO_SR_PRED_INTRO)
  {
    std::vector<Node> tchildren;
    std::vector<Node> sargs = args;
    // take into account witness form, if necessary
    bool reqWitness = d_wfpm.requiresWitnessFormIntro(args[0]);
    Trace("smt-proof-pp-debug")
        << "...pred intro reqWitness=" << reqWitness << std::endl;
    // (TRUE_ELIM
    // (TRANS
    //    (MACRO_SR_EQ_INTRO <children> :args (t args[1:]))
    //    ... proof of apply_SR(t) = toWitness(apply_SR(t)) ...
    //    (MACRO_SR_EQ_INTRO {} {toWitness(apply_SR(t))})
    // ))
    // Notice this is an optimized, one sided version of the expansion of
    // MACRO_SR_PRED_TRANSFORM below.
    // We call the expandMacros method on MACRO_SR_EQ_INTRO, where notice
    // that this rule application is immediately expanded in the recursive
    // call and not added to the proof.
    Node conc = expandMacros(PfRule::MACRO_SR_EQ_INTRO, children, sargs, cdp);
    Trace("smt-proof-pp-debug")
        << "...pred intro conclusion is " << conc << std::endl;
    Assert(!conc.isNull());
    Assert(conc.getKind() == EQUAL);
    Assert(conc[0] == args[0]);
    tchildren.push_back(conc);
    if (reqWitness)
    {
      Node weq = addProofForWitnessForm(conc[1], cdp);
      Trace("smt-proof-pp-debug") << "...weq is " << weq << std::endl;
      if (addToTransChildren(weq, tchildren))
      {
        // toWitness(apply_SR(t)) = apply_SR(toWitness(apply_SR(t)))
        // rewrite again, don't need substitution. Also we always use the
        // default rewriter, due to the definition of MACRO_SR_PRED_INTRO.
        Node weqr = expandMacros(PfRule::MACRO_SR_EQ_INTRO, {}, {weq[1]}, cdp);
        addToTransChildren(weqr, tchildren);
      }
    }
    // apply transitivity if necessary
    Node eq = addProofForTrans(tchildren, cdp);
    Assert(!eq.isNull());
    Assert(eq.getKind() == EQUAL);
    Assert(eq[0] == args[0]);
    Assert(eq[1] == d_true);

    cdp->addStep(eq[0], PfRule::TRUE_ELIM, {eq}, {});
    return eq[0];
  }
  else if (id == PfRule::MACRO_SR_PRED_ELIM)
  {
    // (EQ_RESOLVE
    //   children[0]
    //   (MACRO_SR_EQ_INTRO children[1:] :args children[0] ++ args))
    std::vector<Node> schildren(children.begin() + 1, children.end());
    std::vector<Node> srargs;
    srargs.push_back(children[0]);
    srargs.insert(srargs.end(), args.begin(), args.end());
    Node conc = expandMacros(PfRule::MACRO_SR_EQ_INTRO, schildren, srargs, cdp);
    Assert(!conc.isNull());
    Assert(conc.getKind() == EQUAL);
    Assert(conc[0] == children[0]);
    // apply equality resolve
    cdp->addStep(conc[1], PfRule::EQ_RESOLVE, {children[0], conc}, {});
    return conc[1];
  }
  else if (id == PfRule::MACRO_SR_PRED_TRANSFORM)
  {
    // (EQ_RESOLVE
    //   children[0]
    //   (TRANS
    //      (MACRO_SR_EQ_INTRO children[1:] :args (children[0] args[1:]))
    //      ... proof of c = wc
    //      (MACRO_SR_EQ_INTRO {} wc)
    //      (SYMM
    //        (MACRO_SR_EQ_INTRO children[1:] :args <args>)
    //        ... proof of a = wa
    //        (MACRO_SR_EQ_INTRO {} wa))))
    // where
    // wa = toWitness(apply_SR(args[0])) and
    // wc = toWitness(apply_SR(children[0])).
    Trace("smt-proof-pp-debug")
        << "Transform " << children[0] << " == " << args[0] << std::endl;
    if (CDProof::isSame(children[0], args[0]))
    {
      Trace("smt-proof-pp-debug") << "...nothing to do" << std::endl;
      // nothing to do
      return children[0];
    }
    std::vector<Node> tchildren;
    std::vector<Node> schildren(children.begin() + 1, children.end());
    std::vector<Node> sargs = args;
    // first, compute if we need
    bool reqWitness = d_wfpm.requiresWitnessFormTransform(children[0], args[0]);
    Trace("smt-proof-pp-debug") << "...reqWitness=" << reqWitness << std::endl;
    // convert both sides, in three steps, take symmetry of second chain
    for (unsigned r = 0; r < 2; r++)
    {
      std::vector<Node> tchildrenr;
      // first rewrite children[0], then args[0]
      sargs[0] = r == 0 ? children[0] : args[0];
      // t = apply_SR(t)
      Node eq = expandMacros(PfRule::MACRO_SR_EQ_INTRO, schildren, sargs, cdp);
      Trace("smt-proof-pp-debug")
          << "transform subs_rewrite (" << r << "): " << eq << std::endl;
      Assert(!eq.isNull() && eq.getKind() == EQUAL && eq[0] == sargs[0]);
      addToTransChildren(eq, tchildrenr);
      // apply_SR(t) = toWitness(apply_SR(t))
      if (reqWitness)
      {
        Node weq = addProofForWitnessForm(eq[1], cdp);
        Trace("smt-proof-pp-debug")
            << "transform toWitness (" << r << "): " << weq << std::endl;
        if (addToTransChildren(weq, tchildrenr))
        {
          // toWitness(apply_SR(t)) = apply_SR(toWitness(apply_SR(t)))
          // rewrite again, don't need substitution. Also, we always use the
          // default rewriter, due to the definition of MACRO_SR_PRED_TRANSFORM.
          Node weqr =
              expandMacros(PfRule::MACRO_SR_EQ_INTRO, {}, {weq[1]}, cdp);
          Trace("smt-proof-pp-debug") << "transform rewrite_witness (" << r
                                      << "): " << weqr << std::endl;
          addToTransChildren(weqr, tchildrenr);
        }
      }
      Trace("smt-proof-pp-debug")
          << "transform connect (" << r << ")" << std::endl;
      // add to overall chain
      if (r == 0)
      {
        // add the current chain to the overall chain
        tchildren.insert(tchildren.end(), tchildrenr.begin(), tchildrenr.end());
      }
      else
      {
        // add the current chain to cdp
        Node eqr = addProofForTrans(tchildrenr, cdp);
        if (!eqr.isNull())
        {
          Trace("smt-proof-pp-debug") << "transform connect sym " << tchildren
                                      << " " << eqr << std::endl;
          // take symmetry of above and add it to the overall chain
          addToTransChildren(eqr, tchildren, true);
        }
      }
      Trace("smt-proof-pp-debug")
          << "transform finish (" << r << ")" << std::endl;
    }

    // apply transitivity if necessary
    Node eq = addProofForTrans(tchildren, cdp);

    cdp->addStep(eq[1], PfRule::EQ_RESOLVE, {children[0], eq}, {});
    return args[0];
  }
  else if (id == PfRule::MACRO_RESOLUTION
           || id == PfRule::MACRO_RESOLUTION_TRUST)
  {
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    // first generate the naive chain_resolution
    std::vector<Node> chainResArgs{args.begin() + 1, args.end()};
    Node chainConclusion = d_pc->checkDebug(
        PfRule::CHAIN_RESOLUTION, children, chainResArgs, Node::null(), "");
    Trace("smt-proof-pp-debug") << "Original conclusion: " << args[0] << "\n";
    Trace("smt-proof-pp-debug")
        << "chainRes conclusion: " << chainConclusion << "\n";
    Trace("crowding-lits")
        << "Original conclusion and chainRes conclusion differ\n";
    // There are n cases:
    // - if the conclusion is the same, just replace
    // - if they have the same literals but in different quantity, add a
    //   FACTORING step
    // - if the order is not the same, add a REORDERING step
    // - if there are literals in chainConclusion that are not in the original
    //   conclusion, we need to transform the MACRO_RESOLUTION into a series of
    //   CHAIN_RESOLUTION + FACTORING steps, so that we explicitly eliminate all
    //   these "crowding" literals. We do this via FACTORING so we avoid adding
    //   an exponential number of premises, which would happen if we just
    //   repeated in the premises the clauses needed for eliminating crowding
    //   literals, which could themselves add crowding literals.
    if (chainConclusion == args[0])
    {
      Trace("smt-proof-pp-debug") << "..same conclusion, DONE.\n";
      Trace("crowding-lits") << "..same conclusion, DONE.\n";
      cdp->addStep(
          chainConclusion, PfRule::CHAIN_RESOLUTION, children, chainResArgs);
      return chainConclusion;
    }
    size_t initProofSize = cdp->getNumProofNodes();
    NodeManager* nm = NodeManager::currentNM();
    // If we got here, then chainConclusion is NECESSARILY an OR node
    Assert(chainConclusion.getKind() == kind::OR);
    // get the literals in the chain conclusion
    std::vector<Node> chainConclusionLits{chainConclusion.begin(),
                                          chainConclusion.end()};
    std::set<Node> chainConclusionLitsSet{chainConclusion.begin(),
                                          chainConclusion.end()};
    Trace("smt-proof-pp-debug2")
        << "..chainConclusionLits: " << chainConclusionLits << "\n";
    Trace("smt-proof-pp-debug2")
        << "..chainConclusionLitsSet: " << chainConclusionLitsSet << "\n";
    std::vector<Node> conclusionLits;
    // is args[0] a singleton clause? Yes if it's not an OR node. One might also
    // think that it is a singleton if args[0] occurs in chainConclusionLitsSet.
    // However it's not possible to know this only looking at the sets. For
    // example with
    //
    //  args[0]                : (or b c)
    //  chairConclusionLitsSet : {b, c, (or b c)}
    //
    // we have that if args[0] occurs in the set but as a crowding literal, then
    // args[0] is *not* a singleton clause. But if b and c were crowding
    // literals, then args[0] would be a singleton clause. Since our intention
    // is to determine who are the crowding literals exactly based on whether
    // args[0] is a singleton or not, we must determine in another way whether
    // args[0] is a singleton.
    //
    // Thus we rely on the standard utility to determine if args[0] is singleton
    // based on the premises and arguments of the resolution
    if (proof::isSingletonClause(args[0], children, chainResArgs))
    {
      conclusionLits.push_back(args[0]);
    }
    else
    {
      Assert(args[0].getKind() == kind::OR);
      conclusionLits.insert(
          conclusionLits.end(), args[0].begin(), args[0].end());
    }
    std::set<Node> conclusionLitsSet{conclusionLits.begin(),
                                     conclusionLits.end()};
    // If the sets are different, there are "crowding" literals, i.e. literals
    // that were removed by implicit multi-usage of premises in the resolution
    // chain.
    if (chainConclusionLitsSet != conclusionLitsSet)
    {
      Trace("smt-proof-pp-debug") << "..need to eliminate crowding lits.\n";
      Trace("crowding-lits") << "..need to eliminate crowding lits.\n";
      Trace("crowding-lits") << "..premises: " << children << "\n";
      Trace("crowding-lits") << "..args: " << args << "\n";
      chainConclusion =
          proof::eliminateCrowdingLits(d_env.getOptions().proof.optResReconSize,
                                       chainConclusionLits,
                                       conclusionLits,
                                       children,
                                       args,
                                       cdp,
                                       pnm);
      // update vector of lits. Note that the set is no longer used, so we don't
      // need to update it
      //
      // We need again to check whether chainConclusion is a singleton
      // clause. As above, it's a singleton if it's in the original
      // chainConclusionLitsSet.
      chainConclusionLits.clear();
      if (chainConclusionLitsSet.count(chainConclusion))
      {
        chainConclusionLits.push_back(chainConclusion);
      }
      else
      {
        Assert(chainConclusion.getKind() == kind::OR);
        chainConclusionLits.insert(chainConclusionLits.end(),
                                   chainConclusion.begin(),
                                   chainConclusion.end());
      }
    }
    else
    {
      Trace("smt-proof-pp-debug") << "..add chainRes step directly.\n";
      cdp->addStep(
          chainConclusion, PfRule::CHAIN_RESOLUTION, children, chainResArgs);
    }
    Trace("smt-proof-pp-debug")
        << "Conclusion after chain_res/elimCrowd: " << chainConclusion << "\n";
    Trace("smt-proof-pp-debug")
        << "Conclusion lits: " << chainConclusionLits << "\n";
    // Placeholder for running conclusion
    Node n = chainConclusion;
    // factoring
    if (chainConclusionLits.size() != conclusionLits.size())
    {
      Trace("smt-proof-pp-debug") << "..add factoring step.\n";
      // We build it rather than taking conclusionLits because the order may be
      // different
      std::vector<Node> factoredLits;
      std::unordered_set<TNode> clauseSet;
      for (size_t i = 0, size = chainConclusionLits.size(); i < size; ++i)
      {
        if (clauseSet.count(chainConclusionLits[i]))
        {
          continue;
        }
        factoredLits.push_back(n[i]);
        clauseSet.insert(n[i]);
      }
      Node factored = factoredLits.empty()
                          ? nm->mkConst(false)
                          : factoredLits.size() == 1
                                ? factoredLits[0]
                                : nm->mkNode(kind::OR, factoredLits);
      cdp->addStep(factored, PfRule::FACTORING, {n}, {});
      n = factored;
    }
    // either same node or n as a clause
    Assert(n == args[0] || n.getKind() == kind::OR);
    // reordering
    if (n != args[0])
    {
      Trace("smt-proof-pp-debug") << "..add reordering step.\n";
      cdp->addStep(args[0], PfRule::REORDERING, {n}, {args[0]});
    }
    Trace("crowding-lits") << "Number of added proof nodes: "
                           << cdp->getNumProofNodes() - initProofSize << "\n";
    return args[0];
  }
  else if (id == PfRule::SUBS)
  {
    NodeManager* nm = NodeManager::currentNM();
    // Notice that a naive way to reconstruct SUBS is to do a term conversion
    // proof for each substitution.
    // The proof of f(a) * { a -> g(b) } * { b -> c } = f(g(c)) is:
    //   TRANS( CONG{f}( a=g(b) ), CONG{f}( CONG{g}( b=c ) ) )
    // Notice that more optimal proofs are possible that do a single traversal
    // over t. This is done by applying later substitutions to the range of
    // previous substitutions, until a final simultaneous substitution is
    // applied to t.  For instance, in the above example, we first prove:
    //   CONG{g}( b = c )
    // by applying the second substitution { b -> c } to the range of the first,
    // giving us a proof of g(b)=g(c). We then construct the updated proof
    // by tranitivity:
    //   TRANS( a=g(b), CONG{g}( b=c ) )
    // We then apply the substitution { a -> g(c), b -> c } to f(a), to obtain:
    //   CONG{f}( TRANS( a=g(b), CONG{g}( b=c ) ) )
    // which notice is more compact than the proof above.
    Node t = args[0];
    // get the kind of substitution
    MethodId ids = MethodId::SB_DEFAULT;
    if (args.size() >= 2)
    {
      getMethodId(args[1], ids);
    }
    MethodId ida = MethodId::SBA_SEQUENTIAL;
    if (args.size() >= 3)
    {
      getMethodId(args[2], ida);
    }
    std::vector<std::shared_ptr<CDProof>> pfs;
    std::vector<TNode> vsList;
    std::vector<TNode> ssList;
    std::vector<TNode> fromList;
    std::vector<ProofGenerator*> pgs;
    // first, compute the entire substitution
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      // get the substitution
      builtin::BuiltinProofRuleChecker::getSubstitutionFor(
          children[i], vsList, ssList, fromList, ids);
      // ensure proofs for each formula in fromList
      if (children[i].getKind() == AND && ids == MethodId::SB_DEFAULT)
      {
        for (size_t j = 0, nchildi = children[i].getNumChildren(); j < nchildi;
             j++)
        {
          Node nodej = nm->mkConstInt(Rational(j));
          cdp->addStep(
              children[i][j], PfRule::AND_ELIM, {children[i]}, {nodej});
        }
      }
    }
    std::vector<Node> vvec;
    std::vector<Node> svec;
    for (size_t i = 0, nvs = vsList.size(); i < nvs; i++)
    {
      // Note we process in forward order, since later substitution should be
      // applied to earlier ones, and the last child of a SUBS is processed
      // first.
      TNode var = vsList[i];
      TNode subs = ssList[i];
      TNode childFrom = fromList[i];
      Trace("smt-proof-pp-debug")
          << "...process " << var << " -> " << subs << " (" << childFrom << ", "
          << ids << ")" << std::endl;
      // apply the current substitution to the range
      if (!vvec.empty() && ida == MethodId::SBA_SEQUENTIAL)
      {
        Node ss =
            subs.substitute(vvec.begin(), vvec.end(), svec.begin(), svec.end());
        if (ss != subs)
        {
          Trace("smt-proof-pp-debug")
              << "......updated to " << var << " -> " << ss
              << " based on previous substitution" << std::endl;
          // make the proof for the tranitivity step
          std::shared_ptr<CDProof> pf = std::make_shared<CDProof>(d_env);
          pfs.push_back(pf);
          // prove the updated substitution
          TConvProofGenerator tcg(d_env,
                                  nullptr,
                                  TConvPolicy::ONCE,
                                  TConvCachePolicy::NEVER,
                                  "nested_SUBS_TConvProofGenerator",
                                  nullptr,
                                  true);
          // add previous rewrite steps
          for (unsigned j = 0, nvars = vvec.size(); j < nvars; j++)
          {
            // substitutions are pre-rewrites
            tcg.addRewriteStep(vvec[j], svec[j], pgs[j], true);
          }
          // get the proof for the update to the current substitution
          Node seqss = subs.eqNode(ss);
          std::shared_ptr<ProofNode> pfn = tcg.getProofFor(seqss);
          Assert(pfn != nullptr);
          // add the proof
          pf->addProof(pfn);
          // get proof for childFrom from cdp
          pfn = cdp->getProofFor(childFrom);
          pf->addProof(pfn);
          // ensure we have a proof of var = subs
          Node veqs = addProofForSubsStep(var, subs, childFrom, pf.get());
          // transitivity
          pf->addStep(var.eqNode(ss), PfRule::TRANS, {veqs, seqss}, {});
          // add to the substitution
          vvec.push_back(var);
          svec.push_back(ss);
          pgs.push_back(pf.get());
          continue;
        }
      }
      // Just use equality from CDProof, but ensure we have a proof in cdp.
      // This may involve a TRUE_INTRO/FALSE_INTRO if the substitution step
      // uses the assumption childFrom as a Boolean assignment (e.g.
      // childFrom = true if we are using MethodId::SB_LITERAL).
      addProofForSubsStep(var, subs, childFrom, cdp);
      vvec.push_back(var);
      svec.push_back(subs);
      pgs.push_back(cdp);
    }
    // should be implied by the substitution now
    TConvPolicy tcpolicy = ida == MethodId::SBA_FIXPOINT ? TConvPolicy::FIXPOINT
                                                         : TConvPolicy::ONCE;
    TConvProofGenerator tcpg(d_env,
                             nullptr,
                             tcpolicy,
                             TConvCachePolicy::NEVER,
                             "SUBS_TConvProofGenerator",
                             nullptr,
                             true);
    for (unsigned j = 0, nvars = vvec.size(); j < nvars; j++)
    {
      // substitutions are pre-rewrites
      tcpg.addRewriteStep(vvec[j], svec[j], pgs[j], true);
    }
    // add the proof constructed by the term conversion utility
    std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(t);
    Node eq = pfn->getResult();
    Node ts = builtin::BuiltinProofRuleChecker::applySubstitution(
        t, children, ids, ida);
    Node eqq = t.eqNode(ts);
    // should have the same conclusion, if not, then tcpg does not agree with
    // the substitution.
    if (eq != eqq)
    {
      // this can happen in very rare cases where e.g. x -> a; f(x) -> b
      // and t*{x -> a} = t*{x -> a}*{f(x) -> b} != t*{x -> a, f(x) -> b}
      if (ida == MethodId::SBA_SEQUENTIAL && vsList.size() > 1)
      {
        Trace("smt-proof-pp-debug")
            << "resort to sequential reconstruction" << std::endl;
        // just do the naive sequential reconstruction,
        // (SUBS F1 ... Fn t) ---> (TRANS (SUBS F1 t) ... (SUBS Fn tn))
        Node curr = t;
        std::vector<Node> transChildren;
        for (size_t i = 0, nvs = vsList.size(); i < nvs; i++)
        {
          size_t ii = nvs - 1 - i;
          TNode var = vsList[ii];
          TNode subs = ssList[ii];
          Node next = curr.substitute(var, subs);
          if (next != curr)
          {
            Node eqo = curr.eqNode(next);
            transChildren.push_back(eqo);
            // ensure the proof for the substitution exists
            addProofForSubsStep(var, subs, fromList[ii], cdp);
            // do the single step SUBS on curr with the default arguments
            cdp->addStep(eqo, PfRule::SUBS, {var.eqNode(subs)}, {curr});
            curr = next;
          }
        }
        Assert(curr == ts);
        cdp->addStep(eqq, PfRule::TRANS, transChildren, {});
      }
      else
      {
        Trace("smt-proof-pp-debug")
            << "resort to TRUST_SUBS" << std::endl
            << eq << std::endl
            << eqq << std::endl
            << "from " << children << " applied to " << t << std::endl;
        cdp->addStep(eqq, PfRule::TRUST_SUBS, children, {eqq});
      }
    }
    else
    {
      cdp->addProof(pfn);
    }
    return eqq;
  }
  else if (id == PfRule::REWRITE)
  {
    // get the kind of rewrite
    MethodId idr = MethodId::RW_REWRITE;
    TheoryId theoryId = d_env.theoryOf(args[0]);
    if (args.size() >= 2)
    {
      getMethodId(args[1], idr);
    }
    Rewriter* rr = d_env.getRewriter();
    Node ret = d_env.rewriteViaMethod(args[0], idr);
    Node eq = args[0].eqNode(ret);
    if (idr == MethodId::RW_REWRITE || idr == MethodId::RW_REWRITE_EQ_EXT)
    {
      // rewrites from theory::Rewriter
      bool isExtEq = (idr == MethodId::RW_REWRITE_EQ_EXT);
      // use rewrite with proof interface
      TrustNode trn = rr->rewriteWithProof(args[0], isExtEq);
      std::shared_ptr<ProofNode> pfn = trn.toProofNode();
      if (pfn == nullptr)
      {
        Trace("smt-proof-pp-debug")
            << "Use TRUST_REWRITE for " << eq << std::endl;
        // did not have a proof of rewriting, probably isExtEq is true
        if (isExtEq)
        {
          // update to THEORY_REWRITE with idr
          Assert(args.size() >= 1);
          Node tid = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(theoryId);
          cdp->addStep(eq, PfRule::THEORY_REWRITE, {}, {eq, tid, args[1]});
        }
        else
        {
          // this should never be applied
          cdp->addStep(eq, PfRule::TRUST_REWRITE, {}, {eq});
        }
      }
      else
      {
        cdp->addProof(pfn);
      }
      Assert(trn.getNode() == ret)
          << "Unexpected rewrite " << args[0] << std::endl
          << "Got: " << trn.getNode() << std::endl
          << "Expected: " << ret;
    }
    else if (idr == MethodId::RW_EVALUATE)
    {
      // change to evaluate, which is never eliminated
      cdp->addStep(eq, PfRule::EVALUATE, {}, {args[0]});
    }
    else
    {
      Node retCurr = args[0];
      std::vector<Node> transEq;
      // try to reconstruct the (extended) rewrite
      // first, use the standard rewriter followed by the extended equality
      // rewriter
      for (size_t i = 0; i < 2; i++)
      {
        if (i == 1 && retCurr.getKind() != EQUAL)
        {
          break;
        }
        MethodId midi =
            i == 0 ? MethodId::RW_REWRITE : MethodId::RW_REWRITE_EQ_EXT;
        Node retDef = d_env.rewriteViaMethod(retCurr, midi);
        if (retDef != retCurr)
        {
          // will expand this as a default rewrite if needed
          Node eqd = retCurr.eqNode(retDef);
          Node mid = mkMethodId(midi);
          cdp->addStep(eqd, PfRule::REWRITE, {}, {retCurr, mid});
          transEq.push_back(eqd);
        }
        retCurr = retDef;
        if (retCurr == ret)
        {
          // already successful
          break;
        }
      }
      if (retCurr != ret)
      {
        // try to prove the rewritten form is equal to the extended rewritten
        // form, treated as a stand alone (theory) rewrite
        Node eqp = retCurr.eqNode(ret);
        std::vector<Node> targs;
        targs.push_back(eqp);
        targs.push_back(
            builtin::BuiltinProofRuleChecker::mkTheoryIdNode(theoryId));
        // in this case, must be a non-standard rewrite kind
        Assert(args.size() >= 2);
        targs.push_back(args[1]);
        Node eqpp = expandMacros(PfRule::THEORY_REWRITE, {}, targs, cdp);
        transEq.push_back(eqp);
        if (eqpp.isNull())
        {
          // don't know how to eliminate
          return Node::null();
        }
      }
      if (transEq.size() > 1)
      {
        // put together with transitivity
        cdp->addStep(eq, PfRule::TRANS, transEq, {});
      }
    }
    if (args[0] == ret)
    {
      // should not be necessary typically
      cdp->addStep(eq, PfRule::REFL, {}, {args[0]});
    }
    return eq;
  }
  else if (id == PfRule::MACRO_ARITH_SCALE_SUM_UB)
  {
    Trace("macro::arith") << "Expand MACRO_ARITH_SCALE_SUM_UB" << std::endl;
    if (TraceIsOn("macro::arith"))
    {
      for (const auto& child : children)
      {
        Trace("macro::arith") << "  child: " << child << std::endl;
      }
      Trace("macro::arith") << "   args: " << args << std::endl;
    }
    Assert(args.size() == children.size());
    NodeManager* nm = NodeManager::currentNM();
    ProofStepBuffer steps{d_pc};

    // Scale all children, accumulating
    std::vector<Node> scaledRels;
    for (size_t i = 0; i < children.size(); ++i)
    {
      TNode child = children[i];
      TNode scalar = args[i];
      bool isPos = scalar.getConst<Rational>() > 0;
      Node scalarCmp =
          nm->mkNode(isPos ? GT : LT, scalar, nm->mkConstInt(Rational(0)));
      // (= scalarCmp true)
      Node scalarCmpOrTrue = steps.tryStep(PfRule::EVALUATE, {}, {scalarCmp});
      Assert(!scalarCmpOrTrue.isNull());
      // scalarCmp
      steps.addStep(PfRule::TRUE_ELIM, {scalarCmpOrTrue}, {}, scalarCmp);
      // (and scalarCmp relation)
      Node scalarCmpAndRel =
          steps.tryStep(PfRule::AND_INTRO, {scalarCmp, child}, {});
      Assert(!scalarCmpAndRel.isNull());
      // (=> (and scalarCmp relation) scaled)
      Node impl =
          steps.tryStep(isPos ? PfRule::ARITH_MULT_POS : PfRule::ARITH_MULT_NEG,
                        {},
                        {scalar, child});
      Assert(!impl.isNull());
      // scaled
      Node scaled =
          steps.tryStep(PfRule::MODUS_PONENS, {scalarCmpAndRel, impl}, {});
      Assert(!scaled.isNull());
      scaledRels.emplace_back(scaled);
    }

    Node sumBounds = steps.tryStep(PfRule::ARITH_SUM_UB, scaledRels, {});
    cdp->addSteps(steps);
    Trace("macro::arith") << "Expansion done. Proved: " << sumBounds
                          << std::endl;
    return sumBounds;
  }
  else if (id == PfRule::STRING_INFERENCE)
  {
    // get the arguments
    Node conc;
    InferenceId iid;
    bool isRev;
    std::vector<Node> exp;
    if (theory::strings::InferProofCons::unpackArgs(
            args, conc, iid, isRev, exp))
    {
      if (theory::strings::InferProofCons::convertAndAddProofTo(
              cdp, conc, iid, isRev, exp))
      {
        return conc;
      }
    }
  }
  else if (id == PfRule::BV_BITBLAST)
  {
    bv::BBProof bb(d_env, nullptr, true);
    Node eq = args[0];
    Assert(eq.getKind() == EQUAL);
    bb.bbAtom(eq[0]);
    Node bbAtom = bb.getStoredBBAtom(eq[0]);
    bb.getProofGenerator()->addProofTo(eq[0].eqNode(bbAtom), cdp);
    return eq;
  }
  else if (d_elimAllTrusted && d_pc->getPedanticLevel(id) > 0)
  {
    if (res.isNull())
    {
      res = d_pc->checkDebug(id, children, args);
      Assert(!res.isNull());
    }
    bool reqTrueElim = false;
    // if not an equality, make (= res true).
    if (res.getKind() != EQUAL)
    {
      res = res.eqNode(d_true);
      reqTrueElim = true;
    }
    TheoryId tid = THEORY_LAST;
    MethodId mid = MethodId::RW_REWRITE;
    // if theory rewrite, get diagnostic information
    if (id == PfRule::THEORY_REWRITE)
    {
      builtin::BuiltinProofRuleChecker::getTheoryId(args[1], tid);
      getMethodId(args[2], mid);
    }
    int64_t recLimit = options().proof.proofRewriteRconsRecLimit;
    // attempt to reconstruct the proof of the equality into cdp using the
    // rewrite database proof reconstructor
    if (d_rdbPc.prove(cdp, res[0], res[1], tid, mid, recLimit))
    {
      // If we made (= res true) above, conclude the original res.
      if (reqTrueElim)
      {
        cdp->addStep(res[0], PfRule::TRUE_ELIM, {res}, {});
        res = res[0];
      }
      // if successful, we update the proof
      return res;
    }
    // otherwise no update
  }

  // TRUST, PREPROCESS, THEORY_LEMMA, THEORY_PREPROCESS?

  return Node::null();
}

Node ProofPostprocessCallback::addProofForWitnessForm(Node t, CDProof* cdp)
{
  Node tw = SkolemManager::getOriginalForm(t);
  Node eq = t.eqNode(tw);
  if (t == tw)
  {
    // not necessary, add REFL step
    cdp->addStep(eq, PfRule::REFL, {}, {t});
    return eq;
  }
  std::shared_ptr<ProofNode> pn = d_wfpm.getProofFor(eq);
  if (pn != nullptr)
  {
    // add the proof
    cdp->addProof(pn);
  }
  else
  {
    Assert(false) << "ProofPostprocessCallback::addProofForWitnessForm: failed "
                     "to add proof for witness form of "
                  << t;
  }
  return eq;
}

Node ProofPostprocessCallback::addProofForTrans(
    const std::vector<Node>& tchildren, CDProof* cdp)
{
  size_t tsize = tchildren.size();
  if (tsize > 1)
  {
    Node lhs = tchildren[0][0];
    Node rhs = tchildren[tsize - 1][1];
    Node eq = lhs.eqNode(rhs);
    cdp->addStep(eq, PfRule::TRANS, tchildren, {});
    return eq;
  }
  else if (tsize == 1)
  {
    return tchildren[0];
  }
  return Node::null();
}

Node ProofPostprocessCallback::addProofForSubsStep(Node var,
                                                   Node subs,
                                                   Node assump,
                                                   CDProof* cdp)
{
  // ensure we have a proof of var = subs
  Node veqs = var.eqNode(subs);
  if (veqs != assump)
  {
    // should be true intro or false intro
    Assert(subs.isConst());
    cdp->addStep(
        veqs,
        subs.getConst<bool>() ? PfRule::TRUE_INTRO : PfRule::FALSE_INTRO,
        {assump},
        {});
  }
  return veqs;
}

bool ProofPostprocessCallback::addToTransChildren(Node eq,
                                                  std::vector<Node>& tchildren,
                                                  bool isSymm)
{
  Assert(!eq.isNull());
  Assert(eq.getKind() == kind::EQUAL);
  if (eq[0] == eq[1])
  {
    return false;
  }
  Node equ = isSymm ? eq[1].eqNode(eq[0]) : eq;
  Assert(tchildren.empty()
         || (tchildren[tchildren.size() - 1].getKind() == kind::EQUAL
             && tchildren[tchildren.size() - 1][1] == equ[0]));
  tchildren.push_back(equ);
  return true;
}

ProofPostprocess::ProofPostprocess(Env& env,
                                   rewriter::RewriteDb* rdb,
                                   bool updateScopedAssumptions)
    : EnvObj(env),
      d_cb(env, rdb, updateScopedAssumptions),
      // the update merges subproofs
      d_updater(env, d_cb, options().proof.proofPpMerge),
      d_finalCb(env),
      d_finalizer(env, d_finalCb)
{
}

ProofPostprocess::~ProofPostprocess() {}

void ProofPostprocess::process(std::shared_ptr<ProofNode> pf,
                               ProofGenerator* pppg)
{
  // Initialize the callback, which computes necessary static information about
  // how to process, including how to process assumptions in pf.
  d_cb.initializeUpdate(pppg);
  // now, process
  d_updater.process(pf);
  // take stats and check pedantic
  d_finalCb.initializeUpdate();
  d_finalizer.process(pf);

  std::stringstream serr;
  bool wasPedanticFailure = d_finalCb.wasPedanticFailure(serr);
  if (wasPedanticFailure)
  {
    AlwaysAssert(!wasPedanticFailure)
        << "ProofPostprocess::process: pedantic failure:" << std::endl
        << serr.str();
  }
}

void ProofPostprocess::setEliminateRule(PfRule rule)
{
  d_cb.setEliminateRule(rule);
}

void ProofPostprocess::setEliminateAllTrustedRules()
{
  d_cb.setEliminateAllTrustedRules();
}

}  // namespace smt
}  // namespace cvc5::internal
