/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference to proof conversion.
 */

#include "theory/strings/infer_proof_cons.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Counts the number of times we traverse beneath a "non-core" operator.
 * This is used to reason about substitutions that assume reasoning about
 * concatentation and (dis)equalities only.
 */
class StringCoreTermContext : public TermContext
{
 public:
  StringCoreTermContext() {}
  /** The initial value: not nested. */
  uint32_t initialValue() const override { return 0; }
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override
  {
    if (tval < 2)
    {
      Kind k = t.getKind();
      // kinds we wish to substitute beneath
      if (k == Kind::NOT || k == Kind::EQUAL || k == Kind::STRING_CONCAT)
      {
        return tval;
      }
      return tval + 1;
    }
    return 2;
  }
};

InferProofCons::InferProofCons(Env& env,
                               context::Context* c,
                               SequencesStatistics& statistics)
    : EnvObj(env), d_lazyFactMap(c), d_statistics(statistics)
{
}

void InferProofCons::notifyFact(const InferInfo& ii)
{
  Node fact = ii.d_conc;
  Trace("strings-ipc-notify")
      << "InferProofCons::notifyFact: " << ii << std::endl;
  if (d_lazyFactMap.find(fact) != d_lazyFactMap.end())
  {
    Trace("strings-ipc-notify") << "...duplicate!" << std::endl;
    return;
  }
  Node symFact = CDProof::getSymmFact(fact);
  if (!symFact.isNull() && d_lazyFactMap.find(symFact) != d_lazyFactMap.end())
  {
    Trace("strings-ipc-notify") << "...duplicate (sym)!" << std::endl;
    return;
  }
  std::shared_ptr<InferInfo> iic = std::make_shared<InferInfo>(ii);
  d_lazyFactMap.insert(ii.d_conc, iic);
}

void InferProofCons::notifyLemma(const InferInfo& ii)
{
  d_lazyFactMap[ii.d_conc] = std::make_shared<InferInfo>(ii);
}

void InferProofCons::packArgs(Node conc,
                              InferenceId infer,
                              bool isRev,
                              const std::vector<Node>& exp,
                              std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  args.push_back(conc);
  args.push_back(mkInferenceIdNode(nm, infer));
  args.push_back(nm->mkConst(isRev));
  // The vector exp is stored as arguments; its flatten form are premises. We
  // need both since the grouping of exp is important, e.g. { (and a b), c }
  // is different from { a, b, c } in the convert routine, since positions
  // of formulas in exp have special meaning.
  args.insert(args.end(), exp.begin(), exp.end());
}

bool InferProofCons::unpackArgs(const std::vector<Node>& args,
                                Node& conc,
                                InferenceId& infer,
                                bool& isRev,
                                std::vector<Node>& exp)
{
  Assert(args.size() >= 3);
  conc = args[0];
  if (!getInferenceId(args[1], infer))
  {
    return false;
  }
  isRev = args[2].getConst<bool>();
  exp.insert(exp.end(), args.begin() + 3, args.end());
  return true;
}

/** convert
 *
 * This method converts this call to instructions on what the proof rule
 * step(s) are for concluding the conclusion of the inference. This
 * information is either:
 *
 * (A) stored in the argument ps, which consists of:
 * - A proof rule identifier (ProofStep::d_rule).
 * - The premises of the proof step (ProofStep::d_children).
 * - Arguments to the proof step (ProofStep::d_args).
 *
 * (B) If the proof for the inference cannot be captured by a single
 * step, then the d_rule field of ps is not set, and useBuffer is set to
 * true. In this case, the argument psb is updated to contain (possibly
 * multiple) proof steps for how to construct a proof for the given inference.
 * In particular, psb will contain a set of steps that form a proof
 * whose conclusion is conc and whose free assumptions are exp.
 */
bool InferProofCons::convert(Env& env,
                             InferenceId infer,
                             bool isRev,
                             Node conc,
                             const std::vector<Node>& exp,
                             CDProof* pf)
{
  // now go back and convert it to proof steps and add to proof
  bool useBuffer = false;
  ProofStep ps;
  // ensure proof steps are unique
  TheoryProofStepBuffer psb(pf->getManager()->getChecker(), true);
  // Must flatten children with respect to AND to be ready to explain.
  // We store the index where each flattened vector begins, since some
  // explanations are grouped together using AND.
  std::vector<size_t> startExpIndex;
  for (const Node& ec : exp)
  {
    // store the index in the flattened vector
    startExpIndex.push_back(ps.d_children.size());
    utils::flattenOp(Kind::AND, ec, ps.d_children);
  }
  // debug print
  if (TraceIsOn("strings-ipc-debug"))
  {
    Trace("strings-ipc-debug") << "InferProofCons::convert: " << infer
                               << (isRev ? " :rev " : " ") << conc << std::endl;
    for (const Node& ec : ps.d_children)
    {
      Trace("strings-ipc-debug") << "    e: " << ec << std::endl;
    }
  }
  // try to find a set of proof steps to incorporate into the buffer
  psb.clear();
  // explicitly add ASSUME steps to the proof step buffer for premises of the
  // inference, so that they will not be overwritten in the reconstruction
  // below
  for (const Node& ec : ps.d_children)
  {
    Trace("strings-ipc-debug") << "Explicit add " << ec << std::endl;
    psb.addStep(ProofRule::ASSUME, {}, {ec}, ec);
  }
  NodeManager* nm = NodeManager::currentNM();
  Node nodeIsRev = nm->mkConst(isRev);
  switch (infer)
  {
    // ========================== equal by substitution+rewriting
    case InferenceId::STRINGS_EXTF:
    case InferenceId::STRINGS_EXTF_N:
    case InferenceId::STRINGS_I_NORM_S:
    case InferenceId::STRINGS_I_CONST_MERGE:
    case InferenceId::STRINGS_I_NORM:
    case InferenceId::STRINGS_LEN_NORM:
    case InferenceId::STRINGS_NORMAL_FORM:
    case InferenceId::STRINGS_CODE_PROXY:
    {
      size_t idMax = 0;
      // These three inference assume the substitution is applied to the
      // *arguments* of extended functions and the length function, so we
      // will allow the substitutions to fire in term context value one.
      if (infer == InferenceId::STRINGS_EXTF
          || infer == InferenceId::STRINGS_EXTF_N
          || infer == InferenceId::STRINGS_LEN_NORM)
      {
        idMax = 1;
      }
      // apply the substitution to conclude conc = conc', where conc' is the
      // result of applying the substitution to conc'. This method further
      // concludes conc from conc'. It then remains to prove conc' below.
      Node concr =
          convertCoreSubs(env, pf, psb, conc, ps.d_children, 0, idMax, true);
      Trace("strings-ipc-core") << "Rewrote conclusion" << std::endl;
      Trace("strings-ipc-core") << "- " << conc << std::endl;
      Trace("strings-ipc-core") << "- to " << concr << std::endl;
      if (psb.applyPredIntro(concr, {}))
      {
        useBuffer = true;
      }
    }
    break;
    // ========================== substitution + rewriting
    case InferenceId::STRINGS_RE_NF_CONFLICT:
    case InferenceId::STRINGS_EXTF_D:
    case InferenceId::STRINGS_EXTF_D_N:
    case InferenceId::STRINGS_I_CONST_CONFLICT:
    case InferenceId::STRINGS_UNIT_CONST_CONFLICT:
    case InferenceId::STRINGS_ARITH_BOUND_CONFLICT:
    {
      if (!ps.d_children.empty())
      {
        std::vector<Node> exps(ps.d_children.begin(), ps.d_children.end() - 1);
        Node psrc = ps.d_children[ps.d_children.size() - 1];
        // we apply the substitution on the purified form to get the
        // original conclusion
        if (psb.applyPredTransform(psrc, conc, exps))
        {
          useBuffer = true;
        }
        else
        {
          // More aggressive: lift to original form and use extended rewriting.
          // A common case that this covers is arithmetic bound conflicts like
          // (= (str.len @purifyN) 5) where @purifyN is the purification skolem
          // for (str.++ "ABCDEF" x).
          Node psrco = SkolemManager::getOriginalForm(psrc);
          if (psb.applyPredTransform(psrco,
                                     conc,
                                     exps,
                                     MethodId::SB_DEFAULT,
                                     MethodId::SBA_SEQUENTIAL,
                                     MethodId::RW_EXT_REWRITE))
          {
            useBuffer = psb.applyPredTransform(psrc, psrco, {});
          }
        }
        // Maybe involves AND_ELIM?
        if (!useBuffer)
        {
          Node res = psb.applyPredElim(psrc, exps);
          useBuffer = convertAndElim(nm, res, conc, psb);
        }
      }
      else
      {
        // use the predicate version?
        ps.d_args.push_back(conc);
        ps.d_rule = ProofRule::MACRO_SR_PRED_INTRO;
      }
    }
    break;
    // ========================== rewrite pred
    case InferenceId::STRINGS_EXTF_EQ_REW:
    {
      // the last child is the predicate we are operating on, move to front
      Node src = ps.d_children[ps.d_children.size() - 1];
      Trace("strings-ipc-core")
          << "Generate proof for STRINGS_EXTF_EQ_REW, starting with " << src
          << std::endl;
      // apply the substitution using the proper contextual information
      // using the utility method
      std::vector<Node> expe(ps.d_children.begin(), ps.d_children.end() - 1);
      Node mainEqSRew = convertCoreSubs(env, pf, psb, src, expe, 1, 1);
      Trace("strings-ipc-core") << "...after subs: " << mainEqSRew << std::endl;
      mainEqSRew = psb.applyPredElim(mainEqSRew, {});
      Trace("strings-ipc-core")
          << "...after pred elim: " << mainEqSRew << std::endl;
      if (mainEqSRew == conc)
      {
        Trace("strings-ipc-core") << "...success" << std::endl;
        useBuffer = true;
        break;
      }
      else if (mainEqSRew.getKind() != Kind::EQUAL)
      {
        // Note this can happen in rare cases where substitution+rewriting
        // is more powerful than congruence+rewriting. We fail to reconstruct
        // the proof in this case.
        Trace("strings-ipc-core")
            << "...failed, not equality after rewriting" << std::endl;
        break;
      }
      // may need the "extended equality rewrite"
      Node mainEqSRew2 = psb.applyPredElim(mainEqSRew,
                                           {},
                                           MethodId::SB_DEFAULT,
                                           MethodId::SBA_SEQUENTIAL,
                                           MethodId::RW_REWRITE_EQ_EXT);
      Trace("strings-ipc-core")
          << "...after extended equality rewrite: " << mainEqSRew2 << std::endl;
      // it may have rewritten to an AND, in which case we get the conjunct
      if (convertAndElim(nm, mainEqSRew2, conc, psb))
      {
        useBuffer = true;
        break;
      }
      // rewrite again with default rewriter
      Node mainEqSRew3 = psb.applyPredElim(mainEqSRew2, {});
      useBuffer = (mainEqSRew3 == conc);
    }
    break;
    // ========================== extensionality
    case InferenceId::STRINGS_DEQ_EXTENSIONALITY:
    {
      ps.d_rule = ProofRule::STRING_EXT;
    }
    break;
    // ========================== substitution+rewriting, CONCAT_EQ, ...
    case InferenceId::STRINGS_F_CONST:
    case InferenceId::STRINGS_F_UNIFY:
    case InferenceId::STRINGS_F_ENDPOINT_EMP:
    case InferenceId::STRINGS_F_ENDPOINT_EQ:
    case InferenceId::STRINGS_F_NCTN:
    case InferenceId::STRINGS_N_EQ_CONF:
    case InferenceId::STRINGS_N_CONST:
    case InferenceId::STRINGS_N_UNIFY:
    case InferenceId::STRINGS_N_ENDPOINT_EMP:
    case InferenceId::STRINGS_N_ENDPOINT_EQ:
    case InferenceId::STRINGS_N_NCTN:
    case InferenceId::STRINGS_SSPLIT_CST_PROP:
    case InferenceId::STRINGS_SSPLIT_VAR_PROP:
    case InferenceId::STRINGS_SSPLIT_CST:
    case InferenceId::STRINGS_SSPLIT_VAR:
    {
      Trace("strings-ipc-core") << "Generate core rule for " << infer
                                << " (rev=" << isRev << ")" << std::endl;
      // All of the above inferences have the form:
      //   (explanation for why t and s have the same prefix/suffix) ^
      //   t = s ^
      //   (length constraint)?
      // We call t=s the "main equality" below. The length constraint is
      // optional, which we split on below.
      size_t nchild = ps.d_children.size();
      size_t mainEqIndex = 0;
      bool mainEqIndexSet = false;
      // the length constraint
      std::vector<Node> lenConstraint;
      // these inferences have a length constraint as the last explain
      if (infer == InferenceId::STRINGS_N_UNIFY || infer == InferenceId::STRINGS_F_UNIFY
          || infer == InferenceId::STRINGS_SSPLIT_CST || infer == InferenceId::STRINGS_SSPLIT_VAR
          || infer == InferenceId::STRINGS_SSPLIT_VAR_PROP
          || infer == InferenceId::STRINGS_SSPLIT_CST_PROP)
      {
        if (exp.size() >= 2)
        {
          Assert(exp.size() <= startExpIndex.size());
          // The index of the "main" equality is the last equality before
          // the length explanation.
          mainEqIndex = startExpIndex[exp.size() - 1] - 1;
          mainEqIndexSet = true;
          // the remainder is the length constraint
          lenConstraint.insert(lenConstraint.end(),
                               ps.d_children.begin() + mainEqIndex + 1,
                               ps.d_children.end());
        }
      }
      else if (nchild >= 1)
      {
        // The index of the main equality is the last child.
        mainEqIndex = nchild - 1;
        mainEqIndexSet = true;
      }
      Node mainEq;
      if (mainEqIndexSet)
      {
        mainEq = ps.d_children[mainEqIndex];
        Trace("strings-ipc-core") << "Main equality " << mainEq << " at index "
                                  << mainEqIndex << std::endl;
      }
      if (mainEq.isNull() || mainEq.getKind() != Kind::EQUAL)
      {
        Trace("strings-ipc-core")
            << "...failed to find main equality" << std::endl;
        break;
      }
      // apply MACRO_SR_PRED_ELIM using equalities up to the main eq
      // we purify the core substitution
      std::vector<Node> pcsr(ps.d_children.begin(),
                             ps.d_children.begin() + mainEqIndex);
      Node pmainEq = mainEq;
      // if there are substitutions to apply
      if (mainEqIndex > 0)
      {
        // Compute which equalities we want to flip their substitution.
        // Currently this is only an issue if e.g. (= (str.++ a a) (str.++ b c))
        // where we conclude (= a c) from an explanation (= a b) via
        // STRINGS_F_UNIFY, which would otherwise conclude (= b c) if a -> b
        // was processed as a substitution.
        // In contrast, normal form inferences are truly processed as
        // substitutions in the strings core solver, whereas flat form
        // inferences simply consider unification without substitutions, leading
        // to issues like the one above.
        std::vector<Node> rexp(ps.d_children.begin(),
                               ps.d_children.begin() + mainEqIndex);
        if (infer == InferenceId::STRINGS_F_UNIFY
            || infer == InferenceId::STRINGS_F_ENDPOINT_EQ)
        {
          Trace("strings-ipc-core")
              << "...check reorient substitution" << std::endl;
          Assert(conc.getKind() == Kind::EQUAL);
          // maybe reorient?
          for (size_t i = 0; i < mainEqIndex; i++)
          {
            Assert(rexp[i].getKind() == Kind::EQUAL);
            if (rexp[i][0] == conc[0] || rexp[i][0] == conc[1])
            {
              rexp[i] = rexp[i][1].eqNode(rexp[i][0]);
              Trace("strings-ipc-core")
                  << "...reorient to " << rexp[i] << std::endl;
            }
          }
        }
        // apply substitution using the util method below
        pmainEq = convertCoreSubs(env, pf, psb, mainEq, rexp, 0, 0);
      }
      Trace("strings-ipc-core")
          << "Main equality after subs " << pmainEq << std::endl;
      // now, conclude the proper equality
      Node mainEqSRew = psb.applyPredElim(pmainEq, {});
      if (mainEqSRew == conc)
      {
        Trace("strings-ipc-core") << "...success after rewrite!" << std::endl;
        useBuffer = true;
        break;
      }
      Trace("strings-ipc-core")
          << "Main equality after subs+rewrite " << mainEqSRew << std::endl;
      // now, apply CONCAT_EQ to get the remainder
      std::vector<Node> childrenCeq;
      childrenCeq.push_back(mainEqSRew);
      std::vector<Node> argsCeq;
      argsCeq.push_back(nodeIsRev);
      Node mainEqCeq = psb.tryStep(ProofRule::CONCAT_EQ, childrenCeq, argsCeq);
      Trace("strings-ipc-core")
          << "Main equality after CONCAT_EQ " << mainEqCeq << std::endl;
      if (mainEqCeq.isNull() || mainEqCeq.getKind() != Kind::EQUAL)
      {
        // fail
        break;
      }
      // get the heads of the equality
      std::vector<Node> tvec;
      std::vector<Node> svec;
      theory::strings::utils::getConcat(mainEqCeq[0], tvec);
      theory::strings::utils::getConcat(mainEqCeq[1], svec);
      Node t0 = tvec[isRev ? tvec.size() - 1 : 0];
      Node s0 = svec[isRev ? svec.size() - 1 : 0];
      // Now, mainEqCeq is an equality t ++ ... == s ++ ... where the
      // inference involved t and s.
      if (infer == InferenceId::STRINGS_N_ENDPOINT_EQ
          || infer == InferenceId::STRINGS_N_ENDPOINT_EMP
          || infer == InferenceId::STRINGS_F_ENDPOINT_EQ
          || infer == InferenceId::STRINGS_F_ENDPOINT_EMP)
      {
        // Should be equal to conclusion already, or rewrite to it.
        // Notice that this step is necessary to handle the "rproc"
        // optimization in processSimpleNEq. Alternatively, this could
        // possibly be done by CONCAT_EQ with !isRev.
        std::vector<Node> cexp;
        if (psb.applyPredTransform(mainEqCeq,
                                   conc,
                                   cexp,
                                   MethodId::SB_DEFAULT,
                                   MethodId::SBA_SEQUENTIAL,
                                   MethodId::RW_REWRITE_EQ_EXT))
        {
          Trace("strings-ipc-core") << "Transformed to " << conc
                                    << " via pred transform" << std::endl;
          // success
          useBuffer = true;
          Trace("strings-ipc-core") << "...success!" << std::endl;
        }
        // Otherwise, note that EMP rules conclude ti = "" where
        // t1 ++ ... ++ tn == "". However, these are very rarely applied, let
        // alone for 2+ children. This case is intentionally unhandled here.
      }
      else if (infer == InferenceId::STRINGS_N_CONST || infer == InferenceId::STRINGS_F_CONST
               || infer == InferenceId::STRINGS_N_EQ_CONF)
      {
        // should be a constant conflict
        std::vector<Node> childrenC;
        childrenC.push_back(mainEqCeq);
        // if it is between sequences, we require the explicit disequality
        ProofRule r = ProofRule::CONCAT_CONFLICT;
        if (mainEqCeq[0].getType().isSequence())
        {
          Assert(t0.isConst() && s0.isConst());
          // We introduce an explicit disequality for the constants
          Node deq = t0.eqNode(s0).notNode();
          psb.addStep(ProofRule::MACRO_SR_PRED_INTRO, {}, {deq}, deq);
          Assert(!deq.isNull());
          childrenC.push_back(deq);
          r = ProofRule::CONCAT_CONFLICT_DEQ;
        }
        std::vector<Node> argsC;
        argsC.push_back(nodeIsRev);
        Node conflict = psb.tryStep(r, childrenC, argsC);
        if (conflict == conc)
        {
          useBuffer = true;
          Trace("strings-ipc-core") << "...success!" << std::endl;
        }
        else
        {
          Trace("strings-ipc-core") << "...failed " << conflict << " via " << r
                                    << " " << childrenC << std::endl;
        }
      }
      else if (infer == InferenceId::STRINGS_F_NCTN
               || infer == InferenceId::STRINGS_N_NCTN)
      {
        // May require extended equality rewrite, applied after the rewrite
        // above. Notice we need both in sequence since ext equality rewriting
        // is not recursive.
        std::vector<Node> argsERew;
        addMethodIds(nm,
                     argsERew,
                     MethodId::SB_DEFAULT,
                     MethodId::SBA_SEQUENTIAL,
                     MethodId::RW_REWRITE_EQ_EXT);
        Node mainEqERew =
            psb.tryStep(ProofRule::MACRO_SR_PRED_ELIM, {mainEqCeq}, argsERew);
        if (mainEqERew == conc)
        {
          useBuffer = true;
          Trace("strings-ipc-core") << "...success!" << std::endl;
        }
      }
      else
      {
        bool applySym = false;
        // may need to apply symmetry
        if ((infer == InferenceId::STRINGS_SSPLIT_CST
             || infer == InferenceId::STRINGS_SSPLIT_CST_PROP)
            && t0.isConst())
        {
          Assert(!s0.isConst());
          applySym = true;
          std::swap(t0, s0);
        }
        if (infer == InferenceId::STRINGS_N_UNIFY || infer == InferenceId::STRINGS_F_UNIFY)
        {
          if (conc.getKind() != Kind::EQUAL)
          {
            break;
          }
          // one side should match, the other side could be a split constant
          if (conc[0] != t0 && conc[1] != s0)
          {
            applySym = true;
            std::swap(t0, s0);
          }
          Assert(conc[0].isConst() == t0.isConst());
          Assert(conc[1].isConst() == s0.isConst());
        }
        ProofRule rule = ProofRule::UNKNOWN;
        // the form of the required length constraint expected by the proof
        Node lenReq;
        bool lenSuccess = false;
        if (infer == InferenceId::STRINGS_N_UNIFY || infer == InferenceId::STRINGS_F_UNIFY)
        {
          // the required premise for unify is always len(x) = len(y),
          // however the explanation may not be literally this. Thus, we
          // need to reconstruct a proof from the given explanation.
          // it should be the case that lenConstraint => lenReq.
          // We use terms in the conclusion equality, not t0, s0 here.
          lenReq = nm->mkNode(Kind::STRING_LENGTH, conc[0])
                       .eqNode(nm->mkNode(Kind::STRING_LENGTH, conc[1]));
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_UNIFY;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_VAR)
        {
          // may have to flip
          Assert(conc.getKind() == Kind::AND && conc[0].getKind() == Kind::OR
                 && conc[0][0].getKind() == Kind::EQUAL);
          if (conc[0][0][0] != t0)
          {
            applySym = true;
            std::swap(t0, s0);
          }
          // it should be the case that lenConstraint => lenReq
          lenReq = nm->mkNode(Kind::STRING_LENGTH, t0)
                       .eqNode(nm->mkNode(Kind::STRING_LENGTH, s0))
                       .notNode();
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_SPLIT;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_CST)
        {
          // it should be the case that lenConstraint => lenReq
          lenReq = nm->mkNode(Kind::STRING_LENGTH, t0)
                       .eqNode(nm->mkConstInt(Rational(0)))
                       .notNode();
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_CSPLIT;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_VAR_PROP)
        {
          // it should be the case that lenConstraint => lenReq
          for (unsigned r = 0; r < 2; r++)
          {
            lenReq = nm->mkNode(Kind::GT,
                                nm->mkNode(Kind::STRING_LENGTH, t0),
                                nm->mkNode(Kind::STRING_LENGTH, s0));
            if (convertLengthPf(lenReq, lenConstraint, psb))
            {
              lenSuccess = true;
              break;
            }
            if (r == 0)
            {
              // may be the other direction
              applySym = true;
              std::swap(t0, s0);
            }
          }
          rule = ProofRule::CONCAT_LPROP;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_CST_PROP)
        {
          // it should be the case that lenConstraint => lenReq
          lenReq = nm->mkNode(Kind::STRING_LENGTH, t0)
                       .eqNode(nm->mkConstInt(Rational(0)))
                       .notNode();
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_CPROP;
        }
        if (!lenSuccess)
        {
          Trace("strings-ipc-core")
              << "...failed due to length constraint" << std::endl;
          break;
        }
        // apply symmetry if necessary
        if (applySym)
        {
          std::vector<Node> childrenSymm;
          childrenSymm.push_back(mainEqCeq);
          // note this explicit step may not be necessary
          mainEqCeq = psb.tryStep(ProofRule::SYMM, childrenSymm, {});
          Trace("strings-ipc-core")
              << "Main equality after SYMM " << mainEqCeq << std::endl;
        }
        if (rule != ProofRule::UNKNOWN)
        {
          Trace("strings-ipc-core")
              << "Core rule length requirement is " << lenReq << std::endl;
          // apply the given rule
          std::vector<Node> childrenMain;
          childrenMain.push_back(mainEqCeq);
          childrenMain.push_back(lenReq);
          std::vector<Node> argsMain;
          argsMain.push_back(nodeIsRev);
          Node mainEqMain = psb.tryStep(rule, childrenMain, argsMain);
          Trace("strings-ipc-core") << "Main equality after " << rule << " "
                                    << mainEqMain << std::endl;
          // either equal or rewrites to it
          std::vector<Node> cexp;
          if (psb.applyPredTransform(mainEqMain, conc, cexp))
          {
            // requires that length success is also true
            useBuffer = true;
            Trace("strings-ipc-core") << "...success" << std::endl;
          }
          else
          {
            Trace("strings-ipc-core") << "...fail" << std::endl;
          }
        }
        else
        {
          // should always have given a rule to try above
          Assert(false) << "No reconstruction rule given for " << infer;
        }
      }
    }
    break;
    // ========================== Disequalities
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
    case InferenceId::STRINGS_DEQ_DISL_STRINGS_SPLIT:
    {
      if (conc.getKind() != Kind::AND || conc.getNumChildren() != 2
          || conc[0].getKind() != Kind::EQUAL
          || !conc[0][0].getType().isStringLike()
          || conc[1].getKind() != Kind::EQUAL
          || conc[1][0].getKind() != Kind::STRING_LENGTH)
      {
        Trace("strings-ipc-deq") << "malformed application" << std::endl;
        Assert(false) << "unexpected conclusion " << conc << " for " << infer;
      }
      else
      {
        Node lenReq = nm->mkNode(
            Kind::GEQ, nm->mkNode(Kind::STRING_LENGTH, conc[0][0]), conc[1][1]);
        Trace("strings-ipc-deq")
            << "length requirement is " << lenReq << std::endl;
        if (convertLengthPf(lenReq, ps.d_children, psb))
        {
          Trace("strings-ipc-deq") << "...success length" << std::endl;
          // make the proof
          std::vector<Node> childrenMain;
          childrenMain.push_back(lenReq);
          std::vector<Node> argsMain;
          argsMain.push_back(nodeIsRev);
          Node mainConc =
              psb.tryStep(ProofRule::STRING_DECOMPOSE, childrenMain, argsMain);
          Trace("strings-ipc-deq")
              << "...main conclusion is " << mainConc << std::endl;
          useBuffer = (mainConc == conc);
          if (!useBuffer)
          {
            // Should be made equal by transformation. This step is necessary
            // if rewriting was used to change the skolem introduced in the
            // conclusion.
            useBuffer = psb.applyPredTransform(mainConc, conc, {});
          }
          Trace("strings-ipc-deq")
              << "...success is " << useBuffer << std::endl;
        }
        else
        {
          Assert(false)
              << "Failed to convert length " << lenReq << " " << ps.d_children;
          Trace("strings-ipc-deq") << "...fail length" << std::endl;
        }
      }
    }
    break;
    // ========================== Boolean split
    case InferenceId::STRINGS_CARD_SP:
    case InferenceId::STRINGS_LEN_SPLIT:
    case InferenceId::STRINGS_LEN_SPLIT_EMP:
    case InferenceId::STRINGS_DEQ_DISL_EMP_SPLIT:
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
    case InferenceId::STRINGS_DEQ_STRINGS_EQ:
    case InferenceId::STRINGS_DEQ_LENS_EQ:
    case InferenceId::STRINGS_DEQ_LENGTH_SP:
    case InferenceId::STRINGS_UNIT_SPLIT:
    {
      if (conc.getKind() != Kind::OR)
      {
        // This should never happen. If it does, we resort to using
        // THEORY_INFERENCE_STRINGS below (in production mode).
        Assert(false) << "Expected OR conclusion for " << infer;
      }
      else
      {
        ps.d_rule = ProofRule::SPLIT;
        Assert(ps.d_children.empty());
        ps.d_args.push_back(conc[0]);
      }
    }
    break;
    // ========================== Regular expression unfolding
    case InferenceId::STRINGS_RE_UNFOLD_POS:
    case InferenceId::STRINGS_RE_UNFOLD_NEG:
    {
      Assert (!ps.d_children.empty());
      size_t nchild = ps.d_children.size();
      Node mem = ps.d_children[nchild-1];
      if (nchild>1)
      {
        // if more than one, apply MACRO_SR_PRED_ELIM
        std::vector<Node> tcs;
        tcs.insert(tcs.end(),
                          ps.d_children.begin(),
                          ps.d_children.begin() + (nchild-1));
        mem = psb.applyPredElim(mem, tcs);
        useBuffer = true;
      }
      ProofRule r = ProofRule::UNKNOWN;
      std::vector<Node> args;
      if (mem.isNull())
      {
        // failed to eliminate above
        Assert(false) << "Failed to apply MACRO_SR_PRED_ELIM for RE unfold";
        useBuffer = false;
      }
      else if (infer == InferenceId::STRINGS_RE_UNFOLD_POS)
      {
        r = ProofRule::RE_UNFOLD_POS;
      }
      else
      {
        r = ProofRule::RE_UNFOLD_NEG;
        // it may be an optimized form of concat simplification
        Assert(mem.getKind() == Kind::NOT
               && mem[0].getKind() == Kind::STRING_IN_REGEXP);
        if (mem[0][1].getKind() == Kind::REGEXP_CONCAT)
        {
          bool isCRev;
          Node reLen = RegExpOpr::getRegExpConcatFixed(mem[0][1], isCRev);
          // if we can find a fixed length for a component, use the optimized
          // version
          if (!reLen.isNull())
          {
            r = ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED;
            args.push_back(nm->mkConst(isCRev));
          }
        }
      }
      if (useBuffer)
      {
        mem = psb.tryStep(r, {mem}, args);
        // should match the conclusion
        useBuffer = (mem==conc);
      }
      else
      {
        ps.d_rule = r;
        ps.d_args = args;
      }
    }
    break;
    // ========================== Reduction
    case InferenceId::STRINGS_CTN_POS:
    case InferenceId::STRINGS_CTN_NEG_EQUAL:
    {
      if (ps.d_children.size() != 1)
      {
        break;
      }
      bool polarity = ps.d_children[0].getKind() != Kind::NOT;
      Node atom = polarity ? ps.d_children[0] : ps.d_children[0][0];
      std::vector<Node> args;
      args.push_back(atom);
      Node res = psb.tryStep(ProofRule::STRING_EAGER_REDUCTION, {}, args);
      if (res.isNull())
      {
        break;
      }
      // ite( contains(x,t), x = k1 ++ t ++ k2, x != t )
      std::vector<Node> tiChildren;
      tiChildren.push_back(ps.d_children[0]);
      Node ctnt =
          psb.tryStep(polarity ? ProofRule::TRUE_INTRO : ProofRule::FALSE_INTRO,
                      tiChildren,
                      {});
      if (ctnt.isNull() || ctnt.getKind() != Kind::EQUAL)
      {
        break;
      }
      std::vector<Node> tchildren;
      tchildren.push_back(ctnt);
      // apply substitution { contains(x,t) -> true|false } and rewrite to get
      // conclusion x = k1 ++ t ++ k2 or x != t.
      if (psb.applyPredTransform(res, conc, tchildren))
      {
        useBuffer = true;
      }
    }
    break;

    case InferenceId::STRINGS_REDUCTION:
    {
      size_t nchild = conc.getNumChildren();
      Node mainEq;
      if (conc.getKind() == Kind::EQUAL)
      {
        mainEq = conc;
      }
      else if (conc.getKind() == Kind::AND
               && conc[nchild - 1].getKind() == Kind::EQUAL)
      {
        mainEq = conc[nchild - 1];
      }
      if (mainEq.isNull())
      {
        Trace("strings-ipc-red") << "Bad Reduction: " << conc << std::endl;
        Assert(false) << "Unexpected reduction " << conc;
        break;
      }
      std::vector<Node> argsRed;
      // the left hand side of the last conjunct is the term we are reducing
      argsRed.push_back(mainEq[0]);
      Node red = psb.tryStep(ProofRule::STRING_REDUCTION, {}, argsRed);
      Trace("strings-ipc-red") << "Reduction : " << red << std::endl;
      if (!red.isNull())
      {
        if (red == conc)
        {
          Trace("strings-ipc-red") << "...success!" << std::endl;
          useBuffer = true;
        }
        else
        {
          std::vector<Node> cexp;
          // get the equalities where the reduction is different
          std::vector<Node> matchConds;
          expr::getConversionConditions(red, conc, matchConds);
          Trace("strings-ipc-red")
              << "...need to prove " << matchConds << std::endl;
          // To simplify the proof transformation step below, we manually
          // unpurify skolems from the concluded reduction. This
          // make it more likely the applyPredTransform step does not have to
          // resort to original forms. In particular, the strings rewriter
          // currently does not respect the property that if
          // t ---> c for constant c, then getOriginalForm(t) ---> c. This
          // means we should attempt to replay the term which was used by the
          // strings skolem cache to justify k = c, which is its unpurified
          // form t, not its original form.
          for (const Node& mc : matchConds)
          {
            Node mcu = SkolemManager::getUnpurifiedForm(mc[0]);
            if (mcu != mc[0])
            {
              Node mceq = mc[0].eqNode(mcu);
              psb.addStep(ProofRule::SKOLEM_INTRO, {}, {mc[0]}, mceq);
              cexp.push_back(mceq);
            }
          }
          // either equal or rewrites to it
          if (psb.applyPredTransform(red, conc, cexp))
          {
            Trace("strings-ipc-red") << "...success!" << std::endl;
            useBuffer = true;
          }
          else
          {
            Trace("strings-ipc-red") << "...failed to reduce" << std::endl;
          }
        }
      }
    }
    break;
    // ========================== code injectivity
    case InferenceId::STRINGS_CODE_INJ:
    {
      ps.d_rule = ProofRule::STRING_CODE_INJ;
      Assert(conc.getKind() == Kind::OR && conc.getNumChildren() == 3
             && conc[2].getKind() == Kind::EQUAL);
      ps.d_args.push_back(conc[2][0]);
      ps.d_args.push_back(conc[2][1]);
    }
    break;
    // ========================== unit injectivity
    case InferenceId::STRINGS_UNIT_INJ:
    {
      Assert(conc.getKind() == Kind::EQUAL);
      Assert(ps.d_children.size() == 1
             && ps.d_children[0].getKind() == Kind::EQUAL);
      Node concS =
          psb.tryStep(ProofRule::STRING_SEQ_UNIT_INJ, ps.d_children, {});
      if (!concS.isNull())
      {
        // may need to apply symmetry
        if (concS != conc)
        {
          Node ss = psb.tryStep(ProofRule::SYMM, {concS}, {});
          useBuffer = (ss == conc);
        }
        else
        {
          useBuffer = true;
        }
      }
    }
    break;
    // ========================== prefix conflict
    case InferenceId::STRINGS_PREFIX_CONFLICT:
    case InferenceId::STRINGS_PREFIX_CONFLICT_MIN:
    {
      Trace("strings-ipc-prefix") << "Prefix conflict..." << std::endl;
      std::vector<Node> eqs;
      for (const Node& e : ps.d_children)
      {
        Kind ek = e.getKind();
        if (ek == Kind::EQUAL)
        {
          Trace("strings-ipc-prefix") << "- equality : " << e << std::endl;
          eqs.push_back(e);
        }
        else if (ek == Kind::STRING_IN_REGEXP)
        {
          // unfold it and extract the equality
          std::vector<Node> children;
          children.push_back(e);
          std::vector<Node> args;
          Node eunf = psb.tryStep(ProofRule::RE_UNFOLD_POS, children, args);
          Trace("strings-ipc-prefix")
              << "--- " << e << " unfolds to " << eunf << std::endl;
          if (eunf.isNull())
          {
            continue;
          }
          else if (eunf.getKind() == Kind::AND)
          {
            // equality is the first conjunct
            std::vector<Node> childrenAE;
            childrenAE.push_back(eunf);
            std::vector<Node> argsAE;
            argsAE.push_back(nm->mkConstInt(Rational(0)));
            Node eunfAE = psb.tryStep(ProofRule::AND_ELIM, childrenAE, argsAE);
            Trace("strings-ipc-prefix")
                << "--- and elim to " << eunfAE << std::endl;
            if (eunfAE.isNull() || eunfAE.getKind() != Kind::EQUAL)
            {
              Assert(false)
                  << "Unexpected unfolded premise " << eunf << " for " << infer;
              continue;
            }
            Trace("strings-ipc-prefix")
                << "- equality : " << eunfAE << std::endl;
            eqs.push_back(eunfAE);
          }
          else if (eunf.getKind() == Kind::EQUAL)
          {
            Trace("strings-ipc-prefix") << "- equality : " << eunf << std::endl;
            eqs.push_back(eunf);
          }
        }
        else
        {
          // not sure how to use this assumption
          Assert(false) << "Unexpected premise " << e << " for " << infer;
        }
      }
      if (eqs.empty())
      {
        break;
      }
      // connect via transitivity
      Node curr = eqs[0];
      std::vector<Node> subs;
      for (size_t i = 1, esize = eqs.size(); i < esize; i++)
      {
        Node prev = curr;
        curr = convertTrans(curr, eqs[i], psb);
        // if it is not a transitive step, it corresponds to a substitution
        if (curr.isNull())
        {
          curr = prev;
          // This is an equality between a variable and a concatention or
          // constant term (for example see below).
          // orient the substitution properly
          if (!eqs[i][1].isConst()
              && eqs[i][1].getKind() != Kind::STRING_CONCAT)
          {
            subs.push_back(eqs[i][1].eqNode(eqs[i][0]));
          }
          else
          {
            subs.push_back(eqs[i]);
          }
          continue;
        }
        Trace("strings-ipc-prefix") << "- Via trans: " << curr << std::endl;
      }
      if (curr.isNull())
      {
        break;
      }
      // Substitution is applied in reverse order
      // An example of this inference that uses a substituion is the conflict:
      //  (str.in_re w (re.++ (re.* re.allchar) (str.to_re "ABC")))
      //  (= w (str.++ z y x))
      //  (= x "D")
      // where we apply w -> (str.++ z y x), then x -> "D" to the first
      // predicate to obtain a conflict by rewriting (predicate elim).
      std::reverse(subs.begin(), subs.end());
      Trace("strings-ipc-prefix")
          << "- Possible conflicting equality : " << curr << std::endl;
      Node concE = psb.applyPredElim(curr,
                                     subs,
                                     MethodId::SB_DEFAULT,
                                     MethodId::SBA_SEQUENTIAL,
                                     MethodId::RW_EXT_REWRITE);
      Trace("strings-ipc-prefix")
          << "- After pred elim: " << concE << std::endl;
      if (concE == conc)
      {
        Trace("strings-ipc-prefix") << "...success!" << std::endl;
        useBuffer = true;
      }
    }
    break;
    // ========================== regular expressions
    case InferenceId::STRINGS_RE_INTER_INCLUDE:
    case InferenceId::STRINGS_RE_INTER_CONF:
    case InferenceId::STRINGS_RE_INTER_INFER:
    {
      std::vector<Node> reiExp;
      std::vector<Node> reis;
      std::vector<Node> reiChildren;
      std::vector<Node> reiChildrenOrig;
      Node x;
      // make the regular expression intersection that summarizes all
      // memberships in the explanation
      for (const Node& c : ps.d_children)
      {
        bool polarity = c.getKind() != Kind::NOT;
        Node catom = polarity ? c : c[0];
        if (catom.getKind() != Kind::STRING_IN_REGEXP)
        {
          Assert(c.getKind() == Kind::EQUAL);
          if (c.getKind() == Kind::EQUAL)
          {
            reiExp.push_back(c);
          }
          continue;
        }
        if (x.isNull())
        {
          // just take the first LHS; others should be equated to it by exp
          x = catom[0];
        }
        Node rcurr =
            polarity ? catom[1] : nm->mkNode(Kind::REGEXP_COMPLEMENT, catom[1]);
        reis.push_back(rcurr);
        Node mem = nm->mkNode(Kind::STRING_IN_REGEXP, catom[0], rcurr);
        reiChildren.push_back(mem);
        reiChildrenOrig.push_back(c);
      }
      // go back and justify each premise
      bool successChildren = true;
      for (size_t i = 0, nchild = reiChildren.size(); i < nchild; i++)
      {
        if (!psb.applyPredTransform(reiChildrenOrig[i], reiChildren[i], reiExp))
        {
          Trace("strings-ipc-re")
              << "... failed to justify child " << reiChildren[i] << " from "
              << reiChildrenOrig[i] << std::endl;
          successChildren = false;
          break;
        }
      }
      if (!successChildren)
      {
        break;
      }
      Node mem = psb.tryStep(ProofRule::RE_INTER, reiChildren, {});
      Trace("strings-ipc-re")
          << "Regular expression summary: " << mem << std::endl;
      // the conclusion is rewritable to the premises via rewriting?
      if (psb.applyPredTransform(mem, conc, {}))
      {
        Trace("strings-ipc-re") << "... success!" << std::endl;
        useBuffer = true;
      }
      else
      {
        Trace("strings-ipc-re")
            << "...failed to rewrite to conclusion" << std::endl;
      }
    }
    break;
    case InferenceId::STRINGS_I_CYCLE_E:
    {
      Assert(ps.d_children.size() == 1);
      Node concE = psb.applyPredElim(ps.d_children[0],
                                     {},
                                     MethodId::SB_DEFAULT,
                                     MethodId::SBA_SEQUENTIAL,
                                     MethodId::RW_EXT_REWRITE);
      Trace("strings-ipc-debug") << "... elim to " << concE << std::endl;
      if (concE != conc)
      {
        if (concE.getKind() == Kind::AND)
        {
          for (size_t i = 0, nchild = concE.getNumChildren(); i < nchild; i++)
          {
            if (concE[i] == conc)
            {
              Node ni = nm->mkConstInt(Rational(i));
              psb.addStep(ProofRule::AND_ELIM, {concE}, {ni}, conc);
              useBuffer = true;
              break;
            }
          }
        }
      }
      else
      {
        useBuffer = true;
      }
    }
    break;
    case InferenceId::STRINGS_CTN_DECOMPOSE:
    {
      if (ps.d_children.size() != 2)
      {
        break;
      }
      Node ctn = ps.d_children[0];
      if (ctn.getKind() != Kind::STRING_CONTAINS)
      {
        break;
      }
      Node pconc = psb.tryStep(ProofRule::STRING_EAGER_REDUCTION, {}, {ctn});
      Trace("strings-ipc-cons") << "Eager reduction: " << pconc << std::endl;
      Node pelim = psb.applyPredElim(pconc, {ctn}, MethodId::SB_LITERAL);
      Trace("strings-ipc-cons") << "After rewriting: " << pelim << std::endl;
      if (pelim.getKind() != Kind::EQUAL)
      {
        break;
      }
      Node tgt = ps.d_children[1];
      Node pelim2 = psb.applyPredElim(tgt, {pelim});
      Trace("strings-ipc-cons") << "After elim: " << pelim << std::endl;
      if (pelim2 == conc)
      {
        useBuffer = true;
      }
    }
    break;
    // ========================== unknown and currently unsupported
    case InferenceId::STRINGS_CARDINALITY:
    case InferenceId::STRINGS_I_CYCLE:
    case InferenceId::STRINGS_INFER_EMP:
    case InferenceId::STRINGS_RE_DELTA:
    case InferenceId::STRINGS_RE_DELTA_CONF:
    case InferenceId::STRINGS_RE_DERIVE:
    case InferenceId::STRINGS_FLOOP:
    case InferenceId::STRINGS_FLOOP_CONFLICT:
    case InferenceId::STRINGS_DEQ_NORM_EMP:
    case InferenceId::STRINGS_CTN_TRANS:
    default:
      // do nothing, these will be converted to THEORY_INFERENCE_STRINGS below
      // since the rule is unknown.
      break;
  }

  // now see if we would succeed with the checker-to-try
  bool success = false;
  if (ps.d_rule != ProofRule::UNKNOWN)
  {
    Trace("strings-ipc") << "For " << infer << ", try proof rule " << ps.d_rule
                         << "...";
    Assert(ps.d_rule != ProofRule::UNKNOWN);
    Node pconc = psb.tryStep(ps.d_rule, ps.d_children, ps.d_args);
    if (pconc.isNull() || pconc != conc)
    {
      Trace("strings-ipc") << "failed, pconc is " << pconc << " (expected "
                           << conc << ")" << std::endl;
      ps.d_rule = ProofRule::UNKNOWN;
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
    // successfully set up a multi step proof in psb
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
    if (TraceIsOn("strings-ipc-fail"))
    {
      Trace("strings-ipc-fail")
          << "InferProofCons::convert: Failed " << infer
          << (isRev ? " :rev " : " ") << conc << std::endl;
      for (const Node& ec : exp)
      {
        Trace("strings-ipc-fail") << "    e: " << ec << std::endl;
      }
    }
    //  untrustworthy conversion, the argument of THEORY_INFERENCE_STRINGS is
    //  its conclusion
    ps.d_args.clear();
    ps.d_args.push_back(mkTrustId(nm, TrustId::THEORY_INFERENCE_STRINGS));
    ps.d_args.push_back(conc);
    // use the trust rule
    ps.d_rule = ProofRule::TRUST;
  }
  if (TraceIsOn("strings-ipc-debug"))
  {
    if (useBuffer)
    {
      Trace("strings-ipc-debug")
          << "InferProofCons::convert returned buffer with "
          << psb.getNumSteps() << " steps:" << std::endl;
      const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
      for (const std::pair<Node, ProofStep>& step : steps)
      {
        Trace("strings-ipc-debug")
            << "- " << step.first << " via " << step.second << std::endl;
      }
    }
    else
    {
      Trace("strings-ipc-debug")
          << "InferProofCons::convert returned " << ps << std::endl;
    }
  }
  // make the proof based on the step or the buffer
  if (useBuffer)
  {
    if (!pf->addSteps(psb))
    {
      return false;
    }
  }
  else
  {
    if (!pf->addStep(conc, ps))
    {
      return false;
    }
  }
  return true;
}

bool InferProofCons::convertLengthPf(Node lenReq,
                                     const std::vector<Node>& lenExp,
                                     TheoryProofStepBuffer& psb)
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
  for (const Node& le : lenExp)
  {
    // probably rewrites to it?
    std::vector<Node> exp;
    if (psb.applyPredTransform(le, lenReq, exp))
    {
      Trace("strings-ipc-len") << "...success by rewrite" << std::endl;
      return true;
    }
    // maybe x != "" => len(x) != 0
    std::vector<Node> children;
    children.push_back(le);
    std::vector<Node> args;
    Node res = psb.tryStep(ProofRule::STRING_LENGTH_NON_EMPTY, children, args);
    if (res == lenReq)
    {
      Trace("strings-ipc-len") << "...success by LENGTH_NON_EMPTY" << std::endl;
      return true;
    }
  }
  Trace("strings-ipc-len") << "...failed" << std::endl;
  return false;
}

Node InferProofCons::convertTrans(Node eqa,
                                  Node eqb,
                                  TheoryProofStepBuffer& psb)
{
  if (eqa.getKind() != Kind::EQUAL || eqb.getKind() != Kind::EQUAL)
  {
    return Node::null();
  }
  for (uint32_t i = 0; i < 2; i++)
  {
    Node eqaSym = i == 0 ? eqa[1].eqNode(eqa[0]) : eqa;
    for (uint32_t j = 0; j < 2; j++)
    {
      Node eqbSym = j == 0 ? eqb : eqb[1].eqNode(eqb[0]);
      if (eqa[i] == eqb[j])
      {
        std::vector<Node> children;
        children.push_back(eqaSym);
        children.push_back(eqbSym);
        return psb.tryStep(ProofRule::TRANS, children, {});
      }
    }
  }
  return Node::null();
}

bool InferProofCons::convertAndElim(NodeManager* nm,
                                    const Node& src,
                                    const Node& tgt,
                                    TheoryProofStepBuffer& psb)
{
  if (src == tgt)
  {
    return true;
  }
  Trace("strings-ipc-debug")
      << "AND_ELIM " << src << " => " << tgt << "?" << std::endl;
  Node stgt;
  if (src.getKind() == Kind::NOT && src[0].getKind() == Kind::OR)
  {
    // handles case of ~(L1 or ... or Ln) where tgt is ~Li.
    for (size_t i = 0, nchild = src[0].getNumChildren(); i < nchild; i++)
    {
      Node sn = src[0][i].negate();
      if (CDProof::isSame(sn, tgt))
      {
        Node snn = src[0][i].notNode();
        Node ni = nm->mkConstInt(Rational(i));
        psb.addStep(ProofRule::NOT_OR_ELIM, {src}, {ni}, snn);
        // double negation elimination if necessary
        if (snn != sn)
        {
          psb.addStep(ProofRule::NOT_NOT_ELIM, {snn}, {}, sn);
        }
        stgt = sn;
        break;
      }
    }
  }
  else if (src.getKind() == Kind::AND)
  {
    // otherwise check case of (L1 and ... and Ln) => Li
    for (size_t i = 0, nchild = src.getNumChildren(); i < nchild; i++)
    {
      if (CDProof::isSame(src[i], tgt))
      {
        Node ni = nm->mkConstInt(Rational(i));
        psb.addStep(ProofRule::AND_ELIM, {src}, {ni}, src[i]);
        stgt = src[i];
        break;
      }
    }
  }
  if (!stgt.isNull())
  {
    Assert(CDProof::isSame(stgt, tgt));
    if (stgt != tgt)
    {
      psb.addStep(ProofRule::SYMM, {stgt}, {}, tgt);
    }
    return true;
  }
  return false;
}

Node InferProofCons::convertCoreSubs(Env& env,
                                     CDProof* pf,
                                     TheoryProofStepBuffer& psb,
                                     const Node& src,
                                     const std::vector<Node>& exp,
                                     size_t minIndex,
                                     size_t maxIndex,
                                     bool proveSrc)
{
  // set up the conversion proof generator with string core term context
  StringCoreTermContext sctc;
  TConvProofGenerator tconv(env,
                            nullptr,
                            TConvPolicy::FIXPOINT,
                            TConvCachePolicy::NEVER,
                            "StrTConv",
                            &sctc);
  // add the rewrites for nested contexts up to idMax.
  for (size_t i = minIndex; i <= maxIndex; i++)
  {
    for (const Node& s : exp)
    {
      Trace("strings-ipc-subs")
          << "--- rewrite " << s << ", id " << i << std::endl;
      Assert(s.getKind() == Kind::EQUAL);
      tconv.addRewriteStep(s[0], s[1], pf, false, TrustId::NONE, false, i);
    }
  }
  std::shared_ptr<ProofNode> pfn = tconv.getProofForRewriting(src);
  Node res = pfn->getResult();
  Assert(res.getKind() == Kind::EQUAL);
  if (res[0] != res[1])
  {
    Assert(res[0] == src);
    Trace("strings-ipc-subs") << "Substitutes: " << res << std::endl;
    pf->addProof(pfn);
    // The proof step buffer is tracking unique conclusions, we (dummy) mark
    // that we have a proof of res via the proof above to ensure we do not
    // reprove it.
    psb.addStep(ProofRule::ASSUME, {}, {res}, res);
    if (proveSrc)
    {
      psb.addStep(ProofRule::EQ_RESOLVE, {res[1], res[1].eqNode(src)}, {}, src);
    }
    else
    {
      psb.addStep(ProofRule::EQ_RESOLVE, {src, res}, {}, res[1]);
    }
    return res[1];
  }
  return src;
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  // get the inference
  NodeInferInfoMap::iterator it = d_lazyFactMap.find(fact);
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
  std::shared_ptr<InferInfo> ii = (*it).second;
  Assert(ii->d_conc == fact);
  // make a placeholder proof using STRINGS_INFERENCE, which is reconstructed
  // during post-process
  CDProof pf(d_env);
  std::vector<Node> args;
  packArgs(ii->d_conc, ii->getId(), ii->d_idRev, ii->d_premises, args);
  // must flatten
  std::vector<Node> exp;
  for (const Node& ec : ii->d_premises)
  {
    utils::flattenOp(Kind::AND, ec, exp);
  }
  pf.addStep(fact, ProofRule::MACRO_STRING_INFERENCE, exp, args);
  return pf.getProofFor(fact);
}

std::string InferProofCons::identify() const
{
  return "strings::InferProofCons";
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
