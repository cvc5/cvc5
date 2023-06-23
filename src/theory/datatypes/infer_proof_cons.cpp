/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    if (exp.getKind() == AND)
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
  NodeManager* nm = NodeManager::currentNM();
  bool success = false;
  switch (infer)
  {
    case InferenceId::DATATYPES_UNIF:
    {
      Assert(expv.size() == 1);
      Assert(exp.getKind() == EQUAL && exp[0].getKind() == APPLY_CONSTRUCTOR
             && exp[1].getKind() == APPLY_CONSTRUCTOR
             && exp[0].getOperator() == exp[1].getOperator());
      Node narg;
      // we may be asked for a proof of (not P) coming from (= P false) or
      // (= false P), or similarly P from (= P true) or (= true P).
      bool concPol = conc.getKind() != NOT;
      Node concAtom = concPol ? conc : conc[0];
      Node unifConc = conc;
      for (size_t i = 0, nchild = exp[0].getNumChildren(); i < nchild; i++)
      {
        bool argSuccess = false;
        if (conc.getKind() == EQUAL)
        {
          argSuccess = (exp[0][i] == conc[0] && exp[1][i] == conc[1]);
        }
        else
        {
          for (size_t j = 0; j < 2; j++)
          {
            if (exp[j][i] == concAtom && exp[1 - j][i].isConst()
                && exp[1 - j][i].getConst<bool>() == concPol)
            {
              argSuccess = true;
              unifConc = exp[0][i].eqNode(exp[1][i]);
              break;
            }
          }
        }
        if (argSuccess)
        {
          narg = nm->mkConstInt(Rational(i));
          break;
        }
      }
      if (!narg.isNull())
      {
        if (conc.getKind() == EQUAL)
        {
          // normal case where we conclude an equality
          cdp->addStep(conc, PfRule::DT_UNIF, {exp}, {narg});
        }
        else
        {
          // must use true or false elim to prove the final
          cdp->addStep(unifConc, PfRule::DT_UNIF, {exp}, {narg});
          // may use symmetry
          Node eq = concAtom.eqNode(nm->mkConst(concPol));
          cdp->addStep(
              conc, concPol ? PfRule::TRUE_ELIM : PfRule::FALSE_ELIM, {eq}, {});
        }
        success = true;
      }
    }
    break;
    case InferenceId::DATATYPES_INST:
    {
      if (expv.size() == 1)
      {
        Assert(conc.getKind() == EQUAL);
        int n = utils::isTester(exp);
        if (n >= 0)
        {
          Node t = exp[0];
          Node nn = nm->mkConstInt(Rational(n));
          Node eq = exp.eqNode(conc);
          cdp->addStep(eq, PfRule::DT_INST, {}, {t, nn});
          cdp->addStep(conc, PfRule::EQ_RESOLVE, {exp, eq}, {});
          success = true;
        }
      }
    }
    break;
    case InferenceId::DATATYPES_SPLIT:
    {
      Assert(expv.empty());
      Node t = conc.getKind() == OR ? conc[0][0] : conc[0];
      cdp->addStep(conc, PfRule::DT_SPLIT, {}, {t});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_COLLAPSE_SEL:
    {
      Assert(exp.getKind() == EQUAL);
      Node concEq = conc;
      // might be a Boolean conclusion
      if (conc.getKind() != EQUAL)
      {
        bool concPol = conc.getKind() != NOT;
        Node concAtom = concPol ? conc : conc[0];
        concEq = concAtom.eqNode(nm->mkConst(concPol));
      }
      if (concEq[0].getKind() != APPLY_SELECTOR)
      {
        // can happen for Boolean term variables, which are not currently
        // supported.
        success = false;
      }
      else
      {
        Assert(exp[0].getType().isDatatype());
        Node sop = concEq[0].getOperator();
        Node sl = nm->mkNode(APPLY_SELECTOR, sop, exp[0]);
        Node sr = nm->mkNode(APPLY_SELECTOR, sop, exp[1]);
        // exp[0] = exp[1]
        // --------------------- CONG        ----------------- DT_COLLAPSE
        // s(exp[0]) = s(exp[1])             s(exp[1]) = r
        // --------------------------------------------------- TRANS
        // s(exp[0]) = r
        Node asn = ProofRuleChecker::mkKindNode(APPLY_SELECTOR);
        Node seq = sl.eqNode(sr);
        cdp->addStep(seq, PfRule::CONG, {exp}, {asn, sop});
        Node sceq = sr.eqNode(concEq[1]);
        cdp->addStep(sceq, PfRule::DT_COLLAPSE, {}, {sr});
        cdp->addStep(sl.eqNode(concEq[1]), PfRule::TRANS, {seq, sceq}, {});
        if (conc.getKind() != EQUAL)
        {
          PfRule eid =
              conc.getKind() == NOT ? PfRule::FALSE_ELIM : PfRule::TRUE_ELIM;
          cdp->addStep(conc, eid, {concEq}, {});
        }
        success = true;
      }
    }
    break;
    case InferenceId::DATATYPES_CLASH_CONFLICT:
    {
      cdp->addStep(conc, PfRule::MACRO_SR_PRED_ELIM, {exp}, {});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_TESTER_CONFLICT:
    {
      // rewrites to false under substitution
      Node fn = nm->mkConst(false);
      cdp->addStep(fn, PfRule::MACRO_SR_PRED_ELIM, expv, {});
      success = true;
    }
    break;
    case InferenceId::DATATYPES_TESTER_MERGE_CONFLICT:
    {
      Assert(2 <= expv.size() && expv.size() <= 3);
      Node tester1 = expv[0];
      bool pol = expv[1].getKind() != NOT;
      Node tester2 = pol ? expv[1] : expv[1][0];
      if (tester1.getKind() == APPLY_TESTER
          && tester2.getKind() == APPLY_TESTER)
      {
        Node tester1c =
            nm->mkNode(APPLY_TESTER, tester2.getOperator(), expv[0][0]);
        tester1c = pol ? tester1c : tester1c.notNode();
        if (tester1c != expv[1])
        {
          std::vector<Node> targs{expv[1]};
          if (expv.size() == 3)
          {
            targs.push_back(expv[2]);
          }
          cdp->addStep(
              tester1c, PfRule::MACRO_SR_PRED_TRANSFORM, targs, {tester1c});
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
                     pol ? PfRule::DT_CLASH : PfRule::CONTRA,
                     {tester1, tester1c},
                     {});
        success = true;
      }
    }
    break;
    case InferenceId::DATATYPES_PURIFY:
    {
      cdp->addStep(conc, PfRule::MACRO_SR_PRED_INTRO, {}, {conc});
      success = true;
    }
    break;
    // inferences currently not supported
    case InferenceId::DATATYPES_LABEL_EXH:
    case InferenceId::DATATYPES_BISIMILAR:
    case InferenceId::DATATYPES_CYCLE:
    default:
      Trace("dt-ipc") << "...no conversion for inference " << infer
                      << std::endl;
      break;
  }

  if (!success)
  {
    // failed to reconstruct, add trust
    Trace("dt-ipc") << "...failed " << infer << std::endl;
    Node t = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_DATATYPES);
    cdp->addStep(conc, PfRule::THEORY_INFERENCE, expv, {conc, t});
  }
  else
  {
    Trace("dt-ipc") << "...success" << std::endl;
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
