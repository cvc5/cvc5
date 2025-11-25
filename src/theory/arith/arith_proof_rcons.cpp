/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A generic utility for inferring proofs for arithmetic lemmas.
 */

#include "theory/arith/arith_proof_rcons.h"

#include "proof/conv_proof_generator.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_subs.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

ArithProofRCons::ArithProofRCons(Env& env, TrustId id) : EnvObj(env), d_id(id)
{
  d_false = nodeManager()->mkConst(false);
}

ArithProofRCons::~ArithProofRCons() {}

bool ArithProofRCons::solveEquality(CDProof& cdp,
                                    TConvProofGenerator& tcnv,
                                    ArithSubs& asubs,
                                    const Node& as)
{
  Assert(as.getKind() == Kind::EQUAL);
  Node asr = rewrite(as);
  Trace("arith-proof-rcons") << "...under subs+rewrite: " << asr << std::endl;
  // see if there is a variable to solve for
  std::map<Node, Node> msum;
  // Use rewritten form to get the monomial, we will prove a = as by tcnv
  // and as = (v = val) by MACRO_SR_PRED_TRANSFORM below.
  if (!ArithMSum::getMonomialSumLit(asr, msum))
  {
    Trace("arith-proof-rcons") << "......failed msum" << std::endl;
    return false;
  }
  for (const std::pair<const Node, Node>& m : msum)
  {
    if (m.first.isNull() || !m.second.isNull())
    {
      Trace("arith-proof-rcons") << "......nonfactor " << m.first << " ("
                                 << m.second << ")" << std::endl;
      continue;
    }
    Node veq_c, val;
    int ires = ArithMSum::isolate(m.first, msum, veq_c, val, Kind::EQUAL);
    if (ires == 0 || !veq_c.isNull())
    {
      Trace("arith-proof-rcons") << "......no isolate " << m.first << std::endl;
      continue;
    }
    Trace("arith-proof-rcons")
        << "SUBS: " << m.first << " = " << val << std::endl;
    Node eq = m.first.eqNode(val);
    if (!CDProof::isSame(as, eq))
    {
      cdp.addStep(eq, ProofRule::MACRO_SR_PRED_TRANSFORM, {as}, {eq});
    }
    // to ensure a fixed point substitution, we apply the current
    // substitution to the range of previous substitutions
    if (!asubs.empty())
    {
      ArithSubs stmp;
      stmp.add(m.first, val);
      for (size_t i = 0, ns = asubs.d_subs.size(); i < ns; i++)
      {
        asubs.d_subs[i] = stmp.applyArith(asubs.d_subs[i], false);
      }
    }
    asubs.add(m.first, val);
    tcnv.addRewriteStep(m.first, val, &cdp);
    return true;
  }
  Trace("arith-proof-rcons")
      << "...failed solve equality (no factor)" << std::endl;
  return false;
}

Node ArithProofRCons::applySR(ArithSubs& asubs, const Node& a)
{
  Node as = asubs.applyArith(a, false);
  return rewrite(as);
}

Node ArithProofRCons::applySR(CDProof& cdp,
                              TConvProofGenerator& tcnv,
                              ArithSubs& asubs,
                              const Node& a)
{
  Node as = asubs.applyArith(a, false);
  Node asr = rewrite(as);
  Trace("arith-proof-rcons") << "...have " << asr << std::endl;
  if (a != as)
  {
    std::shared_ptr<ProofNode> pfn = tcnv.getProofForRewriting(a);
    Assert(pfn->getResult()[1] == as)
        << "no-solve: got " << pfn->getResult()[1] << ", expected " << as;
    cdp.addProof(pfn);
    cdp.addStep(as, ProofRule::EQ_RESOLVE, {a, a.eqNode(as)}, {});
  }
  if (!CDProof::isSame(as, asr))
  {
    cdp.addStep(asr, ProofRule::MACRO_SR_PRED_TRANSFORM, {as}, {asr});
  }
  return asr;
}

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
    // Do not traverse non-linear terms
    ArithSubsTermContext astc(false);
    // This proof generator is intended to provide proofs for asubs.applyArith.
    // In particular, we maintain the invariant that if
    // asubs.applyArith(a) = as, then tcnv.getProofForRewriting(a) returns a
    // proof of (= a as).
    TConvProofGenerator tcnv(d_env,
                             nullptr,
                             TConvPolicy::FIXPOINT,
                             TConvCachePolicy::NEVER,
                             "ArithRConsTConv",
                             &astc);
    // if we have not yet found a contradiction, we look for contradictions, or
    // further entailed equalities.
    bool addedSubs = true;
    std::unordered_set<Node> solved;
    while (!success && addedSubs)
    {
      Trace("arith-proof-rcons") << "==== Iterate" << std::endl;
      addedSubs = false;
      // check if two unsolved literals rewrite to the negation of one another
      std::map<Node, bool> pols;
      std::map<Node, Node> psrc;
      std::map<Node, bool>::iterator itp;
      std::map<Node, Node> boundingLits[2];
      for (const Node& a : assumps)
      {
        if (solved.find(a) != solved.end())
        {
          // already solved
          continue;
        }
        Trace("arith-proof-rcons") << "- process " << a << std::endl;
        Node as = asubs.applyArith(a, false);
        Node asr = rewrite(as);
        Trace("arith-proof-rcons") << "  - SR to " << asr << std::endl;
        if (asr == d_false)
        {
          Trace("arith-proof-rcons") << "...success!" << std::endl;
          // apply substitution + rewriting again, with proofs
          applySR(cdp, tcnv, asubs, a);
          success = true;
          break;
        }
        // if its an equality, try to turn it into a substitution
        if (asr.getKind() == Kind::EQUAL)
        {
          // must remember the proof prior to changing the substitution
          std::shared_ptr<ProofNode> pfn;
          if (a != as)
          {
            pfn = tcnv.getProofForRewriting(a);
          }
          if (solveEquality(cdp, tcnv, asubs, as))
          {
            addedSubs = true;
            solved.insert(a);
            if (pfn != nullptr)
            {
              cdp.addProof(pfn);
              cdp.addStep(as, ProofRule::EQ_RESOLVE, {a, a.eqNode(as)}, {});
            }
          }
          continue;
        }
        bool pol = asr.getKind() != Kind::NOT;
        Node aslit = pol ? asr : asr[0];
        itp = pols.find(aslit);
        // look for conflicting atoms
        if (itp != pols.end())
        {
          if (itp->second != pol)
          {
            // apply substitution + rewriting again, with proofs
            Node a1 = applySR(cdp, tcnv, asubs, a);
            Assert(a1 == asr);
            Node a2 = applySR(cdp, tcnv, asubs, psrc[aslit]);
            Assert(a2 == asr.negate());
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
          psrc[aslit] = a;
        }
        // otherwise remember bounds
        if (aslit.getKind() == Kind::GEQ)
        {
          boundingLits[pol ? 0 : 1][aslit[0]] = a;
        }
      }
      // if not successful, see if we can use trichotomy to infer that
      // upper, lower bounds entail an equality.
      if (!success)
      {
        std::map<Node, Node>& bl0 = boundingLits[0];
        std::map<Node, Node>& bl1 = boundingLits[1];
        std::map<Node, Node>::iterator itb;
        Rational negone(-1);
        NodeManager* nm = nodeManager();
        for (const std::pair<const Node, Node>& bl : bl0)
        {
          itb = bl1.find(bl.first);
          if (itb == bl1.end())
          {
            continue;
          }
          // reconstruct the literals of the form
          // (>= t c1) and (not (>= t c2)).
          Node l1 = applySR(asubs, bl.second);
          l1 = l1.getKind() == Kind::NOT ? l1[0] : l1;
          Node l2 = applySR(asubs, itb->second);
          l2 = l2.getKind() == Kind::NOT ? l2[0] : l2;
          Trace("arith-proof-rcons") << "......dual binding lits " << l1
                                     << ", not " << l2 << std::endl;
          Assert(l1.getKind() == Kind::GEQ && l2.getKind() == Kind::GEQ);
          Assert(l1[1].getKind() == Kind::CONST_INTEGER
                 && l2[1].getKind() == Kind::CONST_INTEGER);
          Assert(l1[0] == l2[0]);
          Rational c1 = l1[1].getConst<Rational>();
          Rational c2m1 = l2[1].getConst<Rational>() + negone;
          // if c1 == c2-1, then this implies t = c1.
          if (c1 == c2m1)
          {
            // apply substitution + rewriting with proofs now
            applySR(cdp, tcnv, asubs, bl.second);
            applySR(cdp, tcnv, asubs, itb->second);
            Node l2strict =
                nm->mkNode(Kind::GT, l2[0], nm->mkConstInt(c2m1)).notNode();
            Node l2n = l2.notNode();
            Node equiv = l2n.eqNode(l2strict);
            cdp.addStep(equiv, ProofRule::MACRO_SR_PRED_INTRO, {}, {equiv});
            cdp.addStep(l2strict, ProofRule::EQ_RESOLVE, {l2n, equiv}, {});
            Node eq = l1[0].eqNode(l1[1]);
            cdp.addStep(eq, ProofRule::ARITH_TRICHOTOMY, {l1, l2strict}, {});
            Trace("arith-proof-rcons")
                << ".......solves to " << eq << " by trichotomy" << std::endl;
            if (solveEquality(cdp, tcnv, asubs, eq))
            {
              addedSubs = true;
              solved.insert(bl.second);
              solved.insert(itb->second);
              break;
            }
          }
          // NOTE: otherwise if c1 > c2-1, this implies a contradiction,
          // although it appears that this case does not happen in DIO lemmas.
          // If it did, we would fail with a proof hole here.
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
    Trace("arith-proof-rcons") << "...failed!" << std::endl;
    cdp.addTrustedStep(fact, d_id, {}, {});
  }
  return cdp.getProofFor(fact);
}

std::string ArithProofRCons::identify() const { return "ArithProofRCons"; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
