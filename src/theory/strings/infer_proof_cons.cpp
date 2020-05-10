/*********************                                                        */
/*! \file infer_proof_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference to proof conversion
 **/

#include "theory/strings/infer_proof_cons.h"

#include "expr/proof_skolem_cache.h"
#include "options/strings_options.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(context::Context* c,
                               ProofNodeManager* pnm,
                               SequencesStatistics& statistics,
                               bool pfEnabled)
    : d_pnm(pnm),
      d_lazyFactMap(c),
      d_psb(pnm->getChecker()),
      d_statistics(statistics),
      d_pfEnabled(pfEnabled)
{
}

void InferProofCons::notifyFact(const InferInfo& ii)
{
  Trace("strings-ipc-debug")
      << "InferProofCons::notifyFact: " << ii << std::endl;
  std::shared_ptr<InferInfo> iic = std::make_shared<InferInfo>(ii);
  d_lazyFactMap.insert(ii.d_conc, iic);
}

Node InferProofCons::convert(const InferInfo& ii,
                             ProofStep& ps,
                             bool& useBuffer)
{
  return convert(ii.d_id, ii.d_idRev, ii.d_conc, ii.d_ant, ps, useBuffer);
}

Node InferProofCons::convert(Inference infer,
                             bool isRev,
                             Node conc,
                             const std::vector<Node>& exp,
                             ProofStep& ps,
                             bool& useBuffer)
{
  // the conclusion is the same
  useBuffer = false;
  // Must flatten children with respect to AND to be ready to explain.
  // We store the index where each flattened vector begins, since some
  // explanations are "grouped".
  size_t expIndex = 0;
  std::map<size_t, size_t> startExpIndex;
  for (const Node& ec : exp)
  {
    if (d_pfEnabled)
    {
      // store the index in the flattened vector
      startExpIndex[expIndex] = ps.d_children.size();
      expIndex++;
    }
    utils::flattenOp(AND, ec, ps.d_children);
  }
  // only keep stats if we process it here
  d_statistics.d_inferences << infer;
  if (!d_pfEnabled)
  {
    // don't care about proofs, return now
    d_statistics.d_inferencesNoPf << infer;
    return conc;
  }
  // debug print
  if (Trace.isOn("strings-ipc-debug"))
  {
    Trace("strings-ipc-debug") << "InferProofCons::convert: " << infer
                               << (isRev ? " :rev " : " ") << conc << std::endl;
    for (const Node& ec : exp)
    {
      Trace("strings-ipc-debug") << "    e: " << ec << std::endl;
    }
  }
  // try to find a set of proof steps to incorporate into the buffer
  d_psb.clear();
  NodeManager* nm = NodeManager::currentNM();
  Node nodeIsRev = nm->mkConst(isRev);
  switch (infer)
  {
    // ========================== equal by substitution+rewriting
    case Inference::I_NORM_S:
    case Inference::I_CONST_MERGE:
    case Inference::I_NORM:
    case Inference::LEN_NORM:
    case Inference::NORMAL_FORM:
    case Inference::CODE_PROXY:
    {
      ps.d_args.push_back(conc);
      // will attempt this rule
      ps.d_rule = PfRule::MACRO_SR_PRED_INTRO;
    }
    break;
    // ========================== substitution + rewriting
    case Inference::RE_NF_CONFLICT:
    case Inference::EXTF:
    case Inference::EXTF_N:
    {
      if (conc.isConst())
      {
        std::vector<Node> exps;
        exps.insert(exps.end(), ps.d_children.begin(), ps.d_children.end() - 1);
        Node src = ps.d_children[ps.d_children.size() - 1];
        if (convertPredTransform(src, conc, exps))
        {
          useBuffer = true;
        }
      }
      else
      {
        // use the predicate version
        ps.d_args.push_back(conc);
        ps.d_rule = PfRule::MACRO_SR_PRED_INTRO;
      }
      // minor optimization: apply to LHS of equality (RHS is already reduced)
      // although notice the case above is also a valid proof.
      // ps.d_args.push_back(conc[0]);
      // ps.d_rule = PfRule::MACRO_SR_EQ_INTRO;
      // This doesn't quite work due for symbolic lemmas.
    }
    break;
    // ========================== substitution+rewriting+Boolean entailment
    case Inference::EXTF_D:
    case Inference::EXTF_D_N: break;
    // ========================== equal by substitution+rewriting+rewrite pred
    case Inference::I_CONST_CONFLICT: break;
    // ========================== rewrite pred
    case Inference::EXTF_EQ_REW:
    case Inference::INFER_EMP:
    {
      // need the "extended equality rewrite"
      ps.d_args.push_back(builtin::BuiltinProofRuleChecker::mkRewriterId(
          RewriterId::REWRITE_EQ_EXT));
      ps.d_rule = PfRule::MACRO_SR_PRED_ELIM;
    }
    break;
    // ========================== equal by substitution+rewriting+CTN_NOT_EQUAL
    case Inference::F_NCTN:
    case Inference::N_NCTN: break;
    // ========================== substitution+rewriting, CONCAT_EQ, ...
    case Inference::F_CONST:
    case Inference::F_UNIFY:
    case Inference::F_ENDPOINT_EMP:
    case Inference::F_ENDPOINT_EQ:
    case Inference::N_CONST:
    case Inference::N_UNIFY:
    case Inference::N_ENDPOINT_EMP:
    case Inference::N_ENDPOINT_EQ:
    case Inference::SSPLIT_CST_PROP:
    case Inference::SSPLIT_VAR_PROP:
    case Inference::SSPLIT_CST:
    case Inference::SSPLIT_VAR:
    case Inference::DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
    case Inference::DEQ_DISL_STRINGS_SPLIT:
    {
      Trace("strings-ipc-core") << "Generate core rule for " << infer
                                << " (rev=" << isRev << ")" << std::endl;
      // All of the above inferences have the form:
      //   <explanation for why t and s have the same prefix/suffix> ^
      //   t = s ^
      //  <length constraint>?
      // We call t=s the "main equality" below. The length constraint is
      // optional, which we split on below.
      size_t nchild = ps.d_children.size();
      size_t mainEqIndex = 0;
      bool mainEqIndexSet = false;
      // the length constraint
      std::vector<Node> lenConstraint;
      // these inferences have a length constraint as the last explain
      if (infer == Inference::N_UNIFY || infer == Inference::F_UNIFY
          || infer == Inference::SSPLIT_CST || infer == Inference::SSPLIT_VAR
          || infer == Inference::SSPLIT_VAR_PROP || infer == Inference::SSPLIT_CST_PROP)
      {
        if (exp.size() >= 2)
        {
          std::map<size_t, size_t>::iterator itsei =
              startExpIndex.find(exp.size() - 1);
          if (itsei != startExpIndex.end())
          {
            // The index of the "main" equality is the last equality before
            // the length explanation.
            mainEqIndex = itsei->second - 1;
            mainEqIndexSet = true;
            // the remainder is the length constraint
            lenConstraint.insert(lenConstraint.end(),
                                 ps.d_children.begin() + mainEqIndex + 1,
                                 ps.d_children.end());
          }
        }
      }
      else
      {
        if (nchild >= 1)
        {
          // The index of the main equality is the last child.
          mainEqIndex = nchild - 1;
          mainEqIndexSet = true;
        }
      }
      Node mainEq;
      if (mainEqIndexSet)
      {
        mainEq = ps.d_children[mainEqIndex];
        Trace("strings-ipc-core") << "Main equality " << mainEq << " at index "
                                  << mainEqIndex << std::endl;
      }
      if (mainEq.isNull() || mainEq.getKind() != EQUAL)
      {
        Trace("strings-ipc-core")
            << "...failed to find main equality" << std::endl;
        // Assert(false);
      }
      else
      {
        // apply MACRO_SR_PRED_ELIM using equalities up to the main eq
        std::vector<Node> childrenSRew;
        childrenSRew.push_back(mainEq);
        childrenSRew.insert(childrenSRew.end(),
                            ps.d_children.begin(),
                            ps.d_children.begin() + mainEqIndex);
        std::vector<Node> argsSRew;
        Node mainEqSRew =
            d_psb.tryStep(PfRule::MACRO_SR_PRED_ELIM, childrenSRew, argsSRew);
        if (isSymm(mainEqSRew, mainEq))
        {
          Trace("strings-ipc-core") << "...undo step" << std::endl;
          // not necessary
          d_psb.popStep();
        }
        Trace("strings-ipc-core")
            << "Main equality after subs+rewrite " << mainEqSRew << std::endl;
        // now, apply CONCAT_EQ to get the remainder
        std::vector<Node> childrenCeq;
        childrenCeq.push_back(mainEqSRew);
        std::vector<Node> argsCeq;
        argsCeq.push_back(nodeIsRev);
        Node mainEqCeq = d_psb.tryStep(PfRule::CONCAT_EQ, childrenCeq, argsCeq);
        Trace("strings-ipc-core")
            << "Main equality after CONCAT_EQ " << mainEqCeq << std::endl;
        if (mainEqCeq.isNull() || mainEqCeq.getKind() != EQUAL)
        {
          // fail
          break;
        }
        else if (mainEqCeq == mainEqSRew)
        {
          Trace("strings-ipc-core") << "...undo step" << std::endl;
          // not necessary, probably first component of equality
          d_psb.popStep();
        }
        // Now, mainEqCeq is an equality t ++ ... == s ++ ... where the
        // inference involved t and s.
        if (infer == Inference::N_ENDPOINT_EQ
            || infer == Inference::N_ENDPOINT_EMP
            || infer == Inference::F_ENDPOINT_EQ
            || infer == Inference::F_ENDPOINT_EMP)
        {
          // should be equal to conclusion already, or rewrite to it.
          // Notice that this step is necessary to handle the "rproc"
          // optimization in processSimpleNEq. Alternatively, this could
          // possibly be done by CONCAT_EQ with !isRev.
          std::vector<Node> cexp;
          if (convertPredTransform(
                  mainEqCeq, conc, cexp, RewriterId::REWRITE_EQ_EXT))
          {
            Trace("strings-ipc-core") << "Transformed to " << conc
                                      << " via pred transform" << std::endl;
            // success
            useBuffer = true;
            Trace("strings-ipc-core") << "...success!" << std::endl;
          }
          else
          {
            // TODO: EMP variants are ti = "" where t1 ++ ... ++ tn == "",
            // however, these are very rare applied, let alone for
            // 2+ children.
          }
        }
        else if (infer == Inference::N_CONST || infer == Inference::F_CONST)
        {
          // should be a constant conflict
          std::vector<Node> childrenC;
          childrenC.push_back(mainEqCeq);
          std::vector<Node> argsC;
          argsC.push_back(nodeIsRev);
          Node mainEqC =
              d_psb.tryStep(PfRule::CONCAT_CONFLICT, childrenC, argsC);
          if (mainEqC == conc)
          {
            useBuffer = true;
            Trace("strings-ipc-core") << "...success!" << std::endl;
          }
        }
        else
        {
          std::vector<Node> tvec;
          std::vector<Node> svec;
          utils::getConcat(mainEqCeq[0], tvec);
          utils::getConcat(mainEqCeq[1], svec);
          Node t0 = tvec[isRev ? tvec.size() - 1 : 0];
          Node s0 = svec[isRev ? svec.size() - 1 : 0];
          // may need to apply symmetry
          if ((infer == Inference::SSPLIT_CST
               || infer == Inference::SSPLIT_CST_PROP)
              && t0.isConst())
          {
            Assert(!s0.isConst());
            std::vector<Node> childrenSymm;
            childrenSymm.push_back(mainEqCeq);
            std::vector<Node> argsSymm;
            mainEqCeq = d_psb.tryStep(PfRule::SYMM, childrenSymm, argsSymm);
            Trace("strings-ipc-core")
                << "Main equality after SYMM " << mainEqCeq << std::endl;
            std::swap(t0, s0);
          }
          PfRule rule = PfRule::UNKNOWN;
          // the form of the required length constraint expected by the proof
          Node lenReq;
          if (infer == Inference::N_UNIFY || infer == Inference::F_UNIFY)
          {
            // the required premise for unify is always len(x) = len(y),
            // however the explanation may not be literally this. Thus, we
            // need to reconstruct a proof from the given explanation.
            // it should be the case that lenConstraint => lenReq
            lenReq = nm->mkNode(STRING_LENGTH, t0)
                         .eqNode(nm->mkNode(STRING_LENGTH, s0));
            rule = PfRule::CONCAT_UNIFY;
          }
          else if (infer == Inference::SSPLIT_VAR)
          {
            // it should be the case that lenConstraint => lenReq
            lenReq = nm->mkNode(STRING_LENGTH, t0)
                         .eqNode(nm->mkNode(STRING_LENGTH, s0));
            rule = PfRule::CONCAT_SPLIT;
          }
          else if (infer == Inference::SSPLIT_CST)
          {
            // it should be the case that lenConstraint => lenReq
            lenReq = nm->mkNode(STRING_LENGTH, t0)
                         .eqNode(nm->mkConst(Rational(0)))
                         .notNode();
            rule = PfRule::CONCAT_CSPLIT;
          }
          else if (infer == Inference::SSPLIT_VAR_PROP)
          {
            // it should be the case that lenConstraint => lenReq
            lenReq = nm->mkNode(GT,
                                nm->mkNode(STRING_LENGTH, t0),
                                nm->mkNode(STRING_LENGTH, s0));
            rule = PfRule::CONCAT_LPROP;
          }
          else if (infer == Inference::SSPLIT_CST_PROP)
          {
            // it should be the case that lenConstraint => lenReq
            lenReq = nm->mkNode(STRING_LENGTH, t0)
                         .eqNode(nm->mkConst(Rational(0)))
                         .notNode();
            rule = PfRule::CONCAT_CPROP;
          }
          if (rule != PfRule::UNKNOWN)
          {
            Trace("strings-ipc-core")
                << "Core rule length requirement is " << lenReq << std::endl;
            // must verify it
            bool lenSuccess = convertLengthPf(lenReq, lenConstraint);
            // apply the given rule
            std::vector<Node> childrenMain;
            childrenMain.push_back(mainEqCeq);
            childrenMain.push_back(lenReq);
            std::vector<Node> argsMain;
            argsMain.push_back(nodeIsRev);
            Node mainEqMain = d_psb.tryStep(rule, childrenMain, argsMain);
            Trace("strings-ipc-core") << "Main equality after " << rule << " "
                                      << mainEqMain << std::endl;
            Assert(mainEqMain != mainEqCeq);
            // either equal or rewrites to it
            std::vector<Node> cexp;
            if (convertPredTransform(mainEqMain, conc, cexp))
            {
              // requires that length success is also true
              useBuffer = lenSuccess;
              Trace("strings-ipc-core") << "...success";
            }
            else
            {
              Trace("strings-ipc-core") << "...fail";
            }
            Trace("strings-ipc-core")
                << ", length success = " << lenSuccess << std::endl;
          }
          else
          {
            Assert(false);
          }
        }
      }
    }
    break;
    // ========================== Boolean split
    case Inference::CARD_SP:
    case Inference::LEN_SPLIT:
    case Inference::LEN_SPLIT_EMP:
    case Inference::DEQ_DISL_EMP_SPLIT:
    case Inference::DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
    case Inference::DEQ_STRINGS_EQ:
    case Inference::DEQ_LENS_EQ:
    case Inference::DEQ_LENGTH_SP:
    {
      if (conc.getKind() != OR)
      {
        Assert(false);
      }
      else
      {
        ps.d_rule = PfRule::SPLIT;
        ps.d_args.push_back(conc[0]);
      }
    }
    break;
    // ========================== Regular expression unfolding
    case Inference::RE_UNFOLD_POS:
    case Inference::RE_UNFOLD_NEG:
    {
      ps.d_rule = infer == Inference::RE_UNFOLD_POS ? PfRule::RE_UNFOLD_POS
                                                    : PfRule::RE_UNFOLD_NEG;
    }
    break;
    // ========================== Reduction
    case Inference::CTN_POS: 
    {
      if (ps.d_children.size()==1)
      {
        ps.d_rule = PfRule::STRINGS_EAGER_REDUCTION;
        ps.d_args.push_back(ps.d_children[0]);
        // variant 1 for eager reduction
        ps.d_args.push_back(nm->mkConst(Rational(1)));
      }
    }
      break;
    case Inference::REDUCTION:
    {
      size_t nchild = conc.getNumChildren();
      if (conc.getKind() != AND || conc[nchild - 1].getKind() != EQUAL)
      {
        Assert(false);
      }
      else
      {
        std::vector<Node> childrenRed;
        std::vector<Node> argsRed;
        // the left hand side of the last conjunct is the term we are reducing
        argsRed.push_back(conc[nchild - 1][0]);
        Node red =
            d_psb.tryStep(PfRule::STRINGS_REDUCTION, childrenRed, argsRed);
        if (!red.isNull())
        {
          // either equal or rewrites to it
          std::vector<Node> cexp;
          if (convertPredTransform(red, conc, cexp))
          {
            useBuffer = true;
          }
        }
      }
    }
    break;
    // ========================== Cardinality
    case Inference::CARDINALITY: break;
    // ========================== code injectivity
    case Inference::CODE_INJ: break;

    // ========================== unknown
    case Inference::I_CYCLE_E:
    case Inference::I_CYCLE:
    case Inference::RE_DELTA:
    case Inference::RE_DELTA_CONF:
    case Inference::RE_DERIVE:
    case Inference::FLOOP:
    case Inference::FLOOP_CONFLICT: break;

    // FIXME
    case Inference::DEQ_NORM_EMP:
    case Inference::RE_INTER_INCLUDE:
    case Inference::RE_INTER_CONF:
    case Inference::RE_INTER_INFER:
    case Inference::CTN_TRANS:
    case Inference::CTN_DECOMPOSE:
    case Inference::CTN_NEG_EQUAL:
    default: break;
  }

  // now see if we would succeed with the checker-to-try
  bool success = false;
  if (ps.d_rule != PfRule::UNKNOWN)
  {
    Trace("strings-ipc") << "For " << infer << ", try proof rule " << ps.d_rule
                         << "...";
    Assert(ps.d_rule != PfRule::UNKNOWN);
    Node pconc = d_psb.tryStep(ps.d_rule, ps.d_children, ps.d_args);
    if (pconc.isNull() || pconc != conc)
    {
      Trace("strings-ipc") << "failed, pconc is " << pconc << " (expected "
                           << conc << ")" << std::endl;
      ps.d_rule = PfRule::UNKNOWN;
    }
    else
    {
      // successfully set up a single step proof in ps
      success = true;
      Trace("strings-ipc") << "success!" << std::endl;
    }
  }
  else if (useBuffer)
  {
    // successfully set up a multi step proof in d_psb
    success = true;
  }
  else
  {
    Trace("strings-ipc") << "For " << infer << " " << conc
                         << ", no proof rule, failed" << std::endl;
  }
  if (!success)
  {
    // debug print
    if (Trace.isOn("strings-ipc-fail"))
    {
      Trace("strings-ipc-fail")
          << "InferProofCons::convert: Failed " << infer
          << (isRev ? " :rev " : " ") << conc << std::endl;
      for (const Node& ec : exp)
      {
        Trace("strings-ipc-fail") << "    e: " << ec << std::endl;
      }
    }
    // untrustworthy conversion
    // doesn't expect arguments
    ps.d_args.clear();
    // rule is determined automatically
    ps.d_rule =
        static_cast<PfRule>(static_cast<uint32_t>(PfRule::SIU_BEGIN)
                            + (static_cast<uint32_t>(infer)
                               - static_cast<uint32_t>(Inference::BEGIN)));
    // add to stats
    d_statistics.d_inferencesNoPf << infer;
    if (options::stringPedanticCheck())
    {
      std::stringstream serr;
      serr << "InferProofCons::convert: Failed " << infer
           << (isRev ? " :rev " : " ") << conc << std::endl;
      for (const Node& ec : exp)
      {
        serr << "    e: " << ec << std::endl;
      }
      AlwaysAssert(false) << serr.str();
    }
  }
  if (Trace.isOn("strings-ipc-debug"))
  {
    Trace("strings-ipc-debug") << "InferProofCons::convert returned " << ps
                               << ", useBuffer = " << useBuffer << std::endl;
  }
  return conc;
}

bool InferProofCons::convertLengthPf(Node lenReq,
                                     const std::vector<Node>& lenExp)
{
  for (const Node& le : lenExp)
  {
    if (lenReq == le)
    {
      return true;
    }
  }
  Trace("strings-ipc-len") << "Must explain " << lenReq << " by " << lenExp
                           << std::endl;
  if (lenExp.size() == 1)
  {
    // probably rewrites to it?
    std::vector<Node> exp;
    if (convertPredTransform(lenExp[0], lenReq, exp))
    {
      return true;
    }
    // maybe x != "" => len(x) != 0
    std::vector<Node> children;
    children.push_back(lenExp[0]);
    std::vector<Node> args;
    Node res = d_psb.tryStep(PfRule::LENGTH_NON_EMPTY,children,args);
    if (res==lenReq)
    {
      return true;
    }
  }
  return false;
}

bool InferProofCons::convertPredTransform(Node src,
                                          Node tgt,
                                          const std::vector<Node>& exp,
                                          RewriterId id)
{
  // symmetric equalities
  if (isSymm(src, tgt))
  {
    return true;
  }
  std::vector<Node> children;
  children.push_back(src);
  std::vector<Node> args;
  // try to prove that tgt rewrites to src
  children.insert(children.end(), exp.begin(), exp.end());
  args.push_back(tgt);
  if (id != RewriterId::REWRITE)
  {
    args.push_back(builtin::BuiltinProofRuleChecker::mkRewriterId(id));
  }
  Node res = d_psb.tryStep(PfRule::MACRO_SR_PRED_TRANSFORM, children, args);
  if (res.isNull())
  {
    // failed to apply
    return false;
  }
  // should definitely have concluded tgt
  Assert(res == tgt);
  return true;
}

void InferProofCons::convertPredElim(Node src,
                                     const std::vector<Node>& exp,
                                     RewriterId id)
{
  std::vector<Node> childrenSRew;
  childrenSRew.push_back(src);
  childrenSRew.insert(childrenSRew.end(), exp.begin(), exp.end());
  std::vector<Node> argsSRew;
  Node srcRew =
      d_psb.tryStep(PfRule::MACRO_SR_PRED_ELIM, childrenSRew, argsSRew);
  if (isSymm(src, srcRew))
  {
    d_psb.popStep();
  }
}

bool InferProofCons::isSymm(Node src, Node tgt)
{
  return src == tgt
         || (src.getKind() == EQUAL && tgt.getKind() == EQUAL
             && src[0] == tgt[1] && src[1] == tgt[0]);
}

ProofStepBuffer* InferProofCons::getBuffer() { return &d_psb; }

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  // temporary proof
  CDProof pf(d_pnm);
  // get the inference
  NodeInferInfoMap::iterator it = d_lazyFactMap.find(fact);
  AlwaysAssert(it != d_lazyFactMap.end());
  // now go back and convert it to proof steps and add to proof
  bool useBuffer = false;
  ProofStep ps;
  convert(*(*it).second, ps, useBuffer);
  if (useBuffer)
  {
    if (!pf.addSteps(d_psb))
    {
      return nullptr;
    }
  }
  else
  {
    if (!pf.addStep(fact, ps))
    {
      return nullptr;
    }
  }
  return pf.mkProof(fact);
}

bool InferProofCons::addProofTo(Node fact, CDProof* pf, bool forceOverwrite)
{
  // we copy fresh proofs
  return ProofGenerator::addProofTo(fact, pf, forceOverwrite);
  // TODO: is the alternatve version below necessary?
  // get the inference
  NodeInferInfoMap::iterator it = d_lazyFactMap.find(fact);
  AlwaysAssert(it != d_lazyFactMap.end());
  // now go back and convert it to proof steps and add to proof
  bool useBuffer = false;
  ProofStep ps;
  convert(*(*it).second, ps, useBuffer);
  if (useBuffer)
  {
    return pf->addSteps(d_psb, false, forceOverwrite);
  }
  return pf->addStep(fact, ps, false, forceOverwrite);
}

std::string InferProofCons::identify() const
{
  return "strings::InferProofCons";
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
