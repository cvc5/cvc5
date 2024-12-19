/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A generic utility for infer proofs for arithmetic lemmas.
 */

#include "theory/arith/arith_proof_rcons.h"

#include "expr/term_context.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_subs.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * Arithmetic substitution term context.
 */
class ArithSubsTermContext : public TermContext
{
 public:
  ArithSubsTermContext() {}
  /** The initial value: valid. */
  uint32_t initialValue() const override { return 0; }
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override
  {
    if (tval == 0)
    {
      // if we should not traverse, return 1
      if (!ArithSubs::shouldTraverse(t))
      {
        return 1;
      }
      return 0;
    }
    return tval;
  }
};

ArithProofRCons::ArithProofRCons(Env& env, TrustId id) : EnvObj(env), d_id(id)
{
  d_false = nodeManager()->mkConst(false);
}

ArithProofRCons::~ArithProofRCons() {}

std::shared_ptr<ProofNode> ArithProofRCons::getProofFor(Node fact)
{
  Trace("arith-proof-rcons") << "ArithProofRCons: prove " << fact << std::endl;
  CDProof cdp(d_env);
  bool success = false;
  // ARITH_DIO_LEMMA can typically be reconstructed via substitution+rewriting.
  if (d_id == TrustId::ARITH_DIO_LEMMA)
  {
    Assert(fact.getKind() == Kind::NOT);
    std::vector<Node> assumps;
    if (fact[0].getKind() == Kind::AND)
    {
      assumps.insert(assumps.end(), fact[0].begin(), fact[0].end());
    }
    else
    {
      assumps.push_back(fact[0]);
    }
    ArithSubs asubs;
    std::vector<Node> assumpsNoSolve;
    ArithSubsTermContext astc;
    TConvProofGenerator tcnv(d_env,
                             nullptr,
                             TConvPolicy::ONCE,
                             TConvCachePolicy::NEVER,
                             "ArithRConsTConv",
                             &astc);
    Node tgtAssump;
    // prove false
    for (const Node& a : assumps)
    {
      Trace("arith-proof-rcons") << "Assumption: " << a << std::endl;
      if (a.getKind() != Kind::EQUAL)
      {
        Trace("arith-proof-rcons") << "...not solved" << std::endl;
        assumpsNoSolve.push_back(a);
        continue;
      }
      Node as = asubs.applyArith(a);
      Node asr = rewrite(as);
      Trace("arith-proof-rcons")
          << "...under subs+rewrite: " << asr << std::endl;
      if (asr == d_false)
      {
        Trace("arith-proof-rcons") << "...success!" << std::endl;
        if (a != as)
        {
          std::shared_ptr<ProofNode> pfn = tcnv.getProofForRewriting(a);
          Assert(pfn->getResult()[1] == as);
          cdp.addProof(pfn);
          cdp.addStep(as, ProofRule::EQ_RESOLVE, {a, a.eqNode(as)}, {});
        }
        cdp.addStep(
            d_false, ProofRule::MACRO_SR_PRED_TRANSFORM, {as}, {d_false});
        success = true;
        break;
      }
      // see if there is a variable to solve for
      std::map<Node, Node> msum;
      bool solved = false;
      if (ArithMSum::getMonomialSumLit(as, msum))
      {
        for (const std::pair<const Node, Node>& m : msum)
        {
          if (m.first.isNull() || !m.second.isNull())
          {
            continue;
          }
          Node veq_c, val;
          int ires = ArithMSum::isolate(m.first, msum, veq_c, val, Kind::EQUAL);
          if (ires != 0 && veq_c.isNull())
          {
            solved = true;
            Trace("arith-proof-rcons")
                << "...solved " << m.first << " = " << val << std::endl;
            Node eq = m.first.eqNode(val);
            if (a != as)
            {
              std::shared_ptr<ProofNode> pfn = tcnv.getProofForRewriting(a);
              Assert(pfn->getResult()[1] == as);
              cdp.addProof(pfn);
              cdp.addStep(as, ProofRule::EQ_RESOLVE, {a, a.eqNode(as)}, {});
            }
            if (as != eq)
            {
              cdp.addStep(eq, ProofRule::MACRO_SR_PRED_TRANSFORM, {as}, {eq});
            }
            asubs.add(m.first, val);
            tcnv.addRewriteStep(m.first, val, &cdp);
            break;
          }
        }
      }
      if (!solved)
      {
        Trace("arith-proof-rcons") << "...not solved" << std::endl;
        assumpsNoSolve.push_back(a);
      }
    }
    if (!success)
    {
      Trace("arith-proof-rcons")
          << "Not solved by rewriting single literal" << std::endl;
      // check if two unsolved literals rewrite to the negation of one another
      std::vector<Node> sassumps;
      std::map<Node, bool> pols;
      std::map<Node, bool>::iterator itp;
      for (const Node& a : assumpsNoSolve)
      {
        Node as = asubs.applyArith(a);
        Node asr = rewrite(as);
        Trace("arith-proof-rcons") << "...have " << asr << std::endl;
        if (a != as)
        {
          std::shared_ptr<ProofNode> pfn = tcnv.getProofForRewriting(a);
          Assert(pfn->getResult()[1] == as);
          cdp.addProof(pfn);
          cdp.addStep(as, ProofRule::EQ_RESOLVE, {a, a.eqNode(as)}, {});
        }
        if (as != asr)
        {
          cdp.addStep(asr, ProofRule::MACRO_SR_PRED_TRANSFORM, {as}, {asr});
        }
        bool pol = asr.getKind() != Kind::NOT;
        Node aslit = pol ? asr : asr[0];
        itp = pols.find(aslit);
        if (itp != pols.end())
        {
          if (itp->second != pol)
          {
            Node asn = aslit.notNode();
            cdp.addStep(d_false, ProofRule::CONTRA, {aslit, asn}, {});
            success = true;
            Trace("arith-proof-rcons") << "......contradiction" << std::endl;
            break;
          }
        }
        else
        {
          pols[aslit] = pol;
        }
      }
    }
    if (success)
    {
      cdp.addStep(fact, ProofRule::SCOPE, {d_false}, assumps);
    }
  }
  if (!success)
  {
    cdp.addTrustedStep(fact, d_id, {}, {});
  }
  return cdp.getProofFor(fact);
}

std::string ArithProofRCons::identify() const { return "ArithProofRCons"; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
