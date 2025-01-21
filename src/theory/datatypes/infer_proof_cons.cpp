/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference to proof conversion  for datatypes.
 */

#include "theory/datatypes/infer_proof_cons.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/model_manager.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

InferProofCons::InferProofCons(Env& env, context::Context* c)
    : EnvObj(env), d_lazyFactMap(c == nullptr ? &d_context : c)
{
}

void InferProofCons::notifyFact(const std::shared_ptr<DatatypesInference>& di)
{
  TNode fact = di->d_conc;
  if (d_lazyFactMap.find(fact) != d_lazyFactMap.end())
  {
    return;
  }
  Node symFact = CDProof::getSymmFact(fact);
  if (!symFact.isNull() && d_lazyFactMap.find(symFact) != d_lazyFactMap.end())
  {
    return;
  }
  d_lazyFactMap.insert(fact, di);
}

void InferProofCons::convert(InferenceId infer, TNode conc, TNode exp, CDProof* cdp)
{
  Trace("dt-ipc") << "convert: " << infer << ": " << conc << " by " << exp
                  << std::endl;
  // split into vector
  std::vector<Node> expv;
  if (!exp.isNull() && !exp.isConst())
  {
    if (exp.getKind() == Kind::AND)
    {
      for (const Node& ec : exp)
      {
        expv.push_back(ec);
      }
    }
    else
    {
      expv.push_back(exp);
    }
  }
  NodeManager* nm = nodeManager();
  bool success = false;
  switch (infer)
  {
    case InferenceId::DATATYPES_UNIF:
    {
      Assert(expv.size() == 1);
      Assert(exp.getKind() == Kind::EQUAL
             && exp[0].getKind() == Kind::APPLY_CONSTRUCTOR
             && exp[1].getKind() == Kind::APPLY_CONSTRUCTOR
             && exp[0].getOperator() == exp[1].getOperator());
      Assert(conc.getKind() == Kind::EQUAL);
      Node narg;
      // we may be asked for a proof of (not P) coming from (= P false) or
      // (= false P), or similarly P from (= P true) or (= true P).
      bool concPol = conc.getKind() != Kind::NOT;
      Node concAtom = concPol ? conc : conc[0];
      Node unifConc = conc;
      for (size_t i = 0, nchild = exp[0].getNumChildren(); i < nchild; i++)
      {
        bool argSuccess = false;
        if (exp[0][i] == conc[0] && exp[1][i] == conc[1])
        {
          argSuccess = true;
        }
        else if (exp[0][i] == conc[1] && exp[1][i] == conc[0])
        {
          // it is for the symmetric fact
          argSuccess = true;
          unifConc = conc[1].eqNode(conc[0]);
        }
        if (argSuccess)
        {
          narg = nm->mkConstInt(Rational(i));
          break;
        }
      }
      if (!narg.isNull())
      {
        addDtUnif(cdp, unifConc, exp, narg);
        success = true;
      }
    }
    break;
    case InferenceId::DATATYPES_INST:
    {
      Assert(conc.getKind() == Kind::EQUAL);
      Node tst;
      if (expv.empty())
      {
        // In rare cases, this rule is applied to a constructor without an
        // explanation and introduces purification variables. In this case, it
        // can be shown by MACRO_SR_PRED_INTRO. An example of this would be:
        //   C(a) = C(s(@purify(C(a))))
        // which requires converting to original form and rewriting.
        ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
        Node concc =
            pc->checkDebug(ProofRule::MACRO_SR_PRED_INTRO, {}, {conc}, conc);
        if (concc == conc)
        {
          cdp->addStep(conc, ProofRule::MACRO_SR_PRED_INTRO, {}, {conc});
          success = true;
        }
      }
      else if (expv.size() == 1)
      {
        tst = exp;
      }
      if (!tst.isNull())
      {
        int n = utils::isTester(tst);
        if (n >= 0)
        {
          Node eq = tst.eqNode(conc);
          // ensure the theory rewrite below is correct
          tryRewriteRule(tst, conc, ProofRewriteRule::DT_INST, cdp);
          cdp->addStep(conc, ProofRule::EQ_RESOLVE, {tst, eq}, {});
          success = true;
        }
      }
    }
    break;
    case InferenceId::DATATYPES_SPLIT:
    {
      Assert(expv.empty());
      Node t = conc.getKind() == Kind::OR ? conc[0][0] : conc[0];
      cdp->addStep(conc, ProofRule::DT_SPLIT, {}, {t});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_COLLAPSE_SEL:
    {
      Assert(exp.getKind() == Kind::EQUAL);
      Node concEq = conc;
      // might be a Boolean conclusion
      if (conc.getKind() != Kind::EQUAL)
      {
        bool concPol = conc.getKind() != Kind::NOT;
        Node concAtom = concPol ? conc : conc[0];
        concEq = concAtom.eqNode(nm->mkConst(concPol));
      }
      if (concEq[0].getKind() != Kind::APPLY_SELECTOR)
      {
        // can happen for Boolean term variables, which are not currently
        // supported.
        success = false;
      }
      else
      {
        Assert(exp[0].getType().isDatatype());
        Node sop = concEq[0].getOperator();
        Node sl = nm->mkNode(Kind::APPLY_SELECTOR, sop, exp[0]);
        Node sr = nm->mkNode(Kind::APPLY_SELECTOR, sop, exp[1]);
        // exp[0] = exp[1]
        // --------------------- CONG        ----------------- DT_COLLAPSE
        // s(exp[0]) = s(exp[1])             s(exp[1]) = r
        // --------------------------------------------------- TRANS
        // s(exp[0]) = r
        Node asn = ProofRuleChecker::mkKindNode(nm, Kind::APPLY_SELECTOR);
        Node seq = sl.eqNode(sr);
        std::vector<Node> cargs;
        ProofRule cr = expr::getCongRule(sl, cargs);
        cdp->addStep(seq, cr, {exp}, cargs);
        Node sceq = sr.eqNode(concEq[1]);
        tryRewriteRule(
            sr, concEq[1], ProofRewriteRule::DT_COLLAPSE_SELECTOR, cdp);
        cdp->addStep(sl.eqNode(concEq[1]), ProofRule::TRANS, {seq, sceq}, {});
        if (conc.getKind() != Kind::EQUAL)
        {
          ProofRule eid = conc.getKind() == Kind::NOT ? ProofRule::FALSE_ELIM
                                                      : ProofRule::TRUE_ELIM;
          cdp->addStep(conc, eid, {concEq}, {});
        }
        success = true;
      }
    }
    break;
    case InferenceId::DATATYPES_CLASH_CONFLICT:
    {
      cdp->addStep(conc, ProofRule::MACRO_SR_PRED_ELIM, {exp}, {});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_TESTER_CONFLICT:
    {
      // rewrites to false under substitution
      Node fn = nm->mkConst(false);
      cdp->addStep(fn, ProofRule::MACRO_SR_PRED_ELIM, expv, {});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_TESTER_MERGE_CONFLICT:
    {
      Assert(2 <= expv.size() && expv.size() <= 3);
      Node tester1 = expv[0];
      bool pol = expv[1].getKind() != Kind::NOT;
      Node tester2 = pol ? expv[1] : expv[1][0];
      if (tester1.getKind() == Kind::APPLY_TESTER
          && tester2.getKind() == Kind::APPLY_TESTER)
      {
        Node tester1c =
            nm->mkNode(Kind::APPLY_TESTER, tester2.getOperator(), expv[0][0]);
        tester1c = pol ? tester1c : tester1c.notNode();
        if (tester1c != expv[1])
        {
          std::vector<Node> targs{expv[1]};
          if (expv.size() == 3)
          {
            targs.push_back(expv[2]);
          }
          cdp->addStep(
              tester1c, ProofRule::MACRO_SR_PRED_TRANSFORM, targs, {tester1c});
        }
        Node fn = nm->mkConst(false);
        // if pol is true, it is a conflict is-C1(x) ^ is-C2(x)
        // if pol is false, it is a conflict is-C1(x) ^ ~is-C1(x)
        // In the former case, the proof may be of the form:
        //            is-C2(y)  y = x
        //            ----------------- MACRO_SR_PRED_TRANSFORM
        // is-C1(x)   is-C2(x)
        // ------------------- DT_CLASH
        // false
        cdp->addStep(fn,
                     pol ? ProofRule::DT_CLASH : ProofRule::CONTRA,
                     {tester1, tester1c},
                     {});
        success = true;
      }
    }
    break;
    case InferenceId::DATATYPES_PURIFY:
    {
      cdp->addStep(conc, ProofRule::MACRO_SR_PRED_INTRO, {}, {conc});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_LABEL_EXH:
    {
      // partition to substitution / testers
      std::vector<Node> expvs;
      // placeholder for MACRO_SR_PRED_TRANSFORM below.
      expvs.push_back(Node::null());
      std::vector<Node> expvt;
      std::map<Node, Node> tmap;
      for (const Node& e : expv)
      {
        if (e.getKind() == Kind::NOT && e[0].getKind() == Kind::APPLY_TESTER)
        {
          expvt.push_back(e);
          tmap[e[0].getOperator()] = e;
        }
        else if (e.getKind() == Kind::EQUAL)
        {
          expvs.push_back(e);
        }
      }

      // Exhausted labels. For example, this proves ~is-cons(x) => is-nil(x)
      // We prove this by:
      // ------------------------ DT_SPLIT
      // is-cons(x) or is-nil(x)            ~is-cons(x)
      // ---------------------------------------------- CHAIN_RESOLUTION
      // is-nil(x)
      // The elaboration may be complicated by the fact that the testers are
      // considered modulo equality of their argument.
      // For instance, x=y ^ ~is-cons(x) => is-nil(y) would be another
      // valid input to this elaboration. this is handled below.
      Assert(conc.getKind() == Kind::APPLY_TESTER);
      Node t = conc[0];
      ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
      Node sconc = pc->checkDebug(ProofRule::DT_SPLIT, {}, {t});
      if (!sconc.isNull())
      {
        Trace("dt-ipc") << "...conclude " << sconc << " by split" << std::endl;
        cdp->addStep(sconc, ProofRule::DT_SPLIT, {}, {t});
        Node truen = nm->mkConst(true);
        Node curr = sconc;
        std::vector<Node> premises;
        premises.push_back(sconc);
        std::vector<Node> pols;
        std::vector<Node> lits;
        std::map<Node, Node>::iterator itt;
        for (const Node& e : sconc)
        {
          if (e == conc)
          {
            continue;
          }
          Node en = e.notNode();
          premises.push_back(en);
          pols.emplace_back(truen);
          lits.emplace_back(e);
          // must ensure we have a proof of en
          Assert(e.getKind() == Kind::APPLY_TESTER);
          bool successLit = false;
          itt = tmap.find(e.getOperator());
          if (itt != tmap.end())
          {
            if (itt->second == en)
            {
              successLit = true;
            }
            else
            {
              // otherwise maybe provable modulo equality?
              // This is to handle e.g.
              // (and (not (is-cons x)) (= x y)) => (is-nil y)
              expvs[0] = itt->second;
              Trace("dt-ipc") << "exh-label: " << itt->second << " vs " << en
                              << ", substitution " << expvs << std::endl;
              Node res = pc->checkDebug(
                  ProofRule::MACRO_SR_PRED_TRANSFORM, expvs, {en});
              if (res == en)
              {
                cdp->addStep(
                    res, ProofRule::MACRO_SR_PRED_TRANSFORM, expvs, {en});
                successLit = true;
              }
            }
          }
          if (!successLit)
          {
            curr = Node::null();
            break;
          }
        }
        if (!curr.isNull())
        {
          std::vector<Node> args;
          args.push_back(nm->mkNode(Kind::SEXPR, pols));
          args.push_back(nm->mkNode(Kind::SEXPR, lits));
          curr = pc->checkDebug(ProofRule::CHAIN_RESOLUTION, premises, args);
          if (!curr.isNull())
          {
            Trace("dt-ipc")
                << "...conclude " << curr << " by chain resolution via "
                << premises << std::endl;
            cdp->addStep(curr, ProofRule::CHAIN_RESOLUTION, premises, args);
          }
        }
        success = (curr == conc);
        Assert(success);
      }
    }
    break;
    case InferenceId::DATATYPES_CYCLE:
    {
      // the conflict is of the form
      // (and (= x (C1 ... x1 ...))
      //      (= x1 (C2 ... x2 ...)) ....
      //      (= x{n-1} (Cn ... xn ...))
      //      (= xn (C{n+1} ... x ...)))
      // We take the first n-1 equalities as a substitution and apply it to
      // the right hand side of the last equality, and use DT_CYCLE to derive
      // a conflict.
      Assert(!expv.empty());
      Node lastEq = expv[expv.size() - 1];
      Assert(lastEq.getKind() == Kind::EQUAL);
      std::vector<Node> subs(expv.begin(), expv.begin() + expv.size() - 1);
      ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
      Node eq;
      if (!subs.empty())
      {
        eq = pc->checkDebug(ProofRule::SUBS, subs, {lastEq[1]});
        Assert(!eq.isNull());
        cdp->addStep(eq, ProofRule::SUBS, subs, {lastEq[1]});
      }
      else
      {
        eq = lastEq[1].eqNode(lastEq[1]);
      }
      Node eq1 = lastEq[0].eqNode(eq[1]);
      Trace("dt-ipc-cycle") << "Cycle eq? " << eq1 << std::endl;
      Node falsen =
          d_env.getRewriter()->rewriteViaRule(ProofRewriteRule::DT_CYCLE, eq1);
      if (!falsen.isNull())
      {
        Node eqq = eq1.eqNode(falsen);
        cdp->addTheoryRewriteStep(eqq, ProofRewriteRule::DT_CYCLE);
        cdp->addStep(falsen, ProofRule::EQ_RESOLVE, {eq1, eqq}, {});
        if (eq1 != lastEq)
        {
          cdp->addStep(eq1, ProofRule::TRANS, {lastEq, eq}, {});
        }
        success = true;
      }
    }
    break;
    // inferences currently not supported
    case InferenceId::DATATYPES_BISIMILAR:
    default:
      Trace("dt-ipc") << "...no conversion for inference " << infer
                      << std::endl;
      break;
  }

  if (!success)
  {
    // failed to reconstruct, add trust
    Trace("dt-ipc") << "...failed " << infer << std::endl;
    cdp->addTrustedStep(conc, TrustId::THEORY_INFERENCE_DATATYPES, expv, {});
  }
  else
  {
    Trace("dt-ipc") << "...success" << std::endl;
  }
}

void InferProofCons::tryRewriteRule(TNode a,
                                    TNode b,
                                    ProofRewriteRule r,
                                    CDProof* cdp)
{
  Node eq = a.eqNode(b);
  Node ar = d_env.getRewriter()->rewriteViaRule(r, a);
  if (ar == b)
  {
    cdp->addTheoryRewriteStep(eq, r);
  }
  else
  {
    cdp->addTrustedStep(eq, TrustId::THEORY_INFERENCE_DATATYPES, {}, {});
  }
}

void InferProofCons::addDtUnif(CDProof* cdp,
                               const Node& conc,
                               const Node& exp,
                               const Node& narg)
{
  //                         ---------------------------------------- DT_CONS_EQ
  // C(t1...tn) = C(s1...sn) (C(t1..tn) = C(s1..sn)) = (and t1 = s1 ... tn = sn)
  // ---------------------------------------------------------------- EQ_RESOLVE
  // (and t1 = s1 ... tn = sn)
  // ------------------------ AND_ELIM
  // ti = si
  Node consEq =
      d_env.getRewriter()->rewriteViaRule(ProofRewriteRule::DT_CONS_EQ, exp);
  Assert(!consEq.isNull());
  Node ceq = exp.eqNode(consEq);
  cdp->addTheoryRewriteStep(ceq, ProofRewriteRule::DT_CONS_EQ);
  cdp->addStep(consEq, ProofRule::EQ_RESOLVE, {exp, ceq}, {});
  if (consEq.getKind() == Kind::AND)
  {
    cdp->addStep(conc, ProofRule::AND_ELIM, {consEq}, {narg});
  }
  else
  {
    AlwaysAssert(consEq == conc);
  }
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  Trace("dt-ipc") << "dt-ipc: Ask proof for " << fact << std::endl;
  // temporary proof
  CDProof pf(d_env);
  // get the inference
  NodeDatatypesInferenceMap::iterator it = d_lazyFactMap.find(fact);
  if (it == d_lazyFactMap.end())
  {
    Node factSym = CDProof::getSymmFact(fact);
    if (!factSym.isNull())
    {
      // Use the symmetric fact. There is no need to explictly make a
      // SYMM proof, as this is handled by CDProof::getProofFor below.
      it = d_lazyFactMap.find(factSym);
    }
  }
  AlwaysAssert(it != d_lazyFactMap.end());
  // now go back and convert it to proof steps and add to proof
  std::shared_ptr<DatatypesInference> di = (*it).second;
  // run the conversion
  convert(di->getId(), di->d_conc, di->d_exp, &pf);
  return pf.getProofFor(fact);
}

std::string InferProofCons::identify() const
{
  return "datatypes::InferProofCons";
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
