/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for monomial bound inference lemmas.
 */

#include "theory/arith/nl/ext/flatten_monomial_check.h"

#include "theory/arith/arith_subs.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/uf/equality_engine.h"
#include "util/random.h"
#include "util/rational.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
  
/**
 * A proof generator for lemmas added by the flatten monomial class.
 */
class FlattenMonProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  FlattenMonProofGenerator(Env& env) : EnvObj(env) {}
  virtual ~FlattenMonProofGenerator() {}
  /**
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override
  {
    Trace("nl-ff") << "Flatten monomial getProofFor: " << fact << std::endl;
    Assert (fact.getKind()==Kind::IMPLIES);
    ArithSubsTermContext astc;
    TConvProofGenerator tcnv(d_env,
                             nullptr,
                             TConvPolicy::FIXPOINT,
                             TConvCachePolicy::NEVER,
                             "FlattenMonTConv",
                             &astc);
    CDProof cdp(d_env);
    std::vector<Node> antec;
    if (fact[0].getKind()==Kind::AND)
    {
      antec.insert(antec.end(), fact[0].begin(), fact[0].end());
    }
    else {
      antec.push_back(fact[0]);
    }
    for (const Node& a : antec)
    {
      Assert (a.getKind()==Kind::EQUAL);
      tcnv.addRewriteStep(a[0], a[1], &cdp);
    }
    Node conc = fact[1];
    std::shared_ptr<ProofNode> pfn = tcnv.getProofForRewriting(conc[0]);
    if (pfn->getResult()==conc)
    {
      cdp.addProof(pfn);
      cdp.addStep(fact, ProofRule::SCOPE, {conc}, antec);
    }
    else
    {
      cdp.addTrustedStep(fact, TrustId::ARITH_NL_FLATTEN_MON_LEMMA, {}, {});
    }
    return cdp.getProofFor(fact);
  }
  /** identify */
  std::string identify() const override { return "FlattenMonProofGenerator"; }
};

FlattenMonomialCheck::FlattenMonomialCheck(Env& env,
                                           TheoryState& astate,
                                           InferenceManager& im)
    : EnvObj(env), d_astate(astate), d_im(im), d_pfgen(d_env.isTheoryProofProducing()
                   ? new 
class FlattenMonProofGenerator(d_env)
                   : nullptr)
{
}

void FlattenMonomialCheck::check(const std::vector<Node>& mvec)
{
  Trace("nl-ff") << "=== Compute flatten eq" << std::endl;
  Trace("nl-ff") << "vars: " << mvec << std::endl;
  std::unordered_set<Node> mvs(mvec.begin(), mvec.end());
  ArithSubs as;
  std::map<Node, Node> repsProcessed;
  std::map<Node, Node>::iterator itr;
  // Mapping normalized terms t to the term s such that applying the
  // substitution as to s gives t.
  std::map<Node, Node> ffMap;
  eq::EqualityEngine* ee = d_astate.getEqualityEngine();
  Trace("nl-ff") << "Equality engine: " << ee->debugPrintEqc() << std::endl;
  eq::EqClassesIterator eqcsi = eq::EqClassesIterator(ee);
  Rational rone(1);
  while (!eqcsi.isFinished())
  {
    Node vr = (*eqcsi);
    ++eqcsi;
    if (!vr.getType().isRealOrInt())
    {
      continue;
    }
    Trace("nl-ff") << "- Representative " << vr << std::endl;
    // find a legal non-linear mult term in its equivalence class
    eq::EqClassIterator eqci = eq::EqClassIterator(vr, ee);
    std::unordered_set<Node> baseTerms;
    std::vector<Node> nlTerms;
    Node one;
    Node firstBaseTerm;
    while (!eqci.isFinished())
    {
      Node n = (*eqci);
      if (n.getKind() == Kind::NONLINEAR_MULT)
      {
        nlTerms.push_back(n);
        Trace("nl-ff") << "  - mult: " << n << std::endl;
      }
      else if (n.isConst())
      {
        if (n.getConst<Rational>() == rone)
        {
          one = n;
        }
        // ignore other constants
      }
      else if (mvs.find(n) != mvs.end())
      {
        baseTerms.insert(n);
        if (firstBaseTerm.isNull())
        {
          firstBaseTerm = n;
        }
        Trace("nl-ff") << "  - var: " << n << std::endl;
      }
      ++eqci;
    }
    std::shuffle(nlTerms.begin(), nlTerms.end(), Random::getRandom());
    Node rep;
    // one is always used as the representative, which is intuitively the empty
    // multiplication
    if (!one.isNull())
    {
      rep = one;
      nlTerms.clear();
    }
    // try to find an NL term that does not induce a cycle with any baseTerm
    for (const Node& n : nlTerms)
    {
      Node ns = rewrite(as.applyArith(n));
      std::map<Node, size_t> ff;
      Assert(ns.getKind() != Kind::MULT);
      if (ns.getKind() == Kind::NONLINEAR_MULT)
      {
        for (const Node& nsc : ns)
        {
          ff[nsc]++;
        }
      }
      else
      {
        ff[ns]++;
      }
      bool cyclic = false;
      for (std::pair<const Node, size_t>& f : ff)
      {
        if (baseTerms.find(f.first) != baseTerms.end())
        {
          Trace("nl-ff") << "*** Cyclic: " << n << " == " << ns
                         << ", in equivalence class of " << f.first
                         << std::endl;
          cyclic = true;
          break;
        }
      }
      if (!cyclic)
      {
        rep = ns;
      }
      // add to flatten map, which may recognize an inference
      addToFlattenMonMap(ns, n, ffMap, repsProcessed);
    }
    if (baseTerms.empty())
    {
      Trace("nl-ff") << "...no base terms, continue." << std::endl;
      // don't care
      continue;
    }
    if (rep.isNull())
    {
      if (baseTerms.size() == 1)
      {
        Trace("nl-ff")
            << "...only one base term, no (acyclic) nl term, continue."
            << std::endl;
        // don't care
        continue;
      }
      rep = firstBaseTerm;
    }
    Trace("nl-ff") << "...choose rep: " << rep << std::endl;
    Assert(!rep.isNull());
    // map all base terms to representative
    ArithSubs asTmp;
    for (const Node& b : baseTerms)
    {
      if (b != rep)
      {
        asTmp.add(b, rep);
      }
    }
    // apply to range
    for (size_t i = 0, ns = as.d_subs.size(); i < ns; i++)
    {
      as.d_subs[i] = asTmp.applyArith(as.d_subs[i]);
    }
    as.append(asTmp);
    repsProcessed[vr] = rep;
    std::map<Node, Node> ffMapNew;
    std::vector<Node> ffMapOld;
    for (std::pair<const Node, Node>& ff : ffMap)
    {
      Node fnew = asTmp.applyArith(ff.first);
      if (fnew != ff.first)
      {
        fnew = rewrite(fnew);
        ffMapNew[fnew] = ff.second;
        ffMapOld.emplace_back(ff.first);
      }
    }
    for (const Node& f : ffMapOld)
    {
      ffMap.erase(f);
    }
    for (std::pair<const Node, Node>& ff : ffMapNew)
    {
      addToFlattenMonMap(ff.first, ff.second, ffMap, repsProcessed);
    }
  }
  if (TraceIsOn("nl-ff"))
  {
    Trace("nl-ff") << "Final flat form:" << std::endl;
    for (std::pair<const Node, Node>& ff : ffMap)
    {
      Trace("nl-ff") << "  " << ff.first << " <- " << ff.second << std::endl;
    }
    Trace("nl-ff") << "Final substitution:" << std::endl;
    for (size_t i = 0, ns = as.d_subs.size(); i < ns; i++)
    {
      Trace("nl-ff") << "  " << as.d_vars[i] << " |-> " << as.d_subs[i]
                     << std::endl;
    }
  }
}

void FlattenMonomialCheck::addToFlattenMonMap(const Node& ns,
                                              const Node& n,
                                              std::map<Node, Node>& ffMap,
                                              const std::map<Node, Node>& repEq)
{
  std::map<Node, Node>::const_iterator itr = ffMap.find(ns);
  if (itr == ffMap.end())
  {
    ffMap[ns] = n;
    return;
  }
  // if not already equal
  if (d_astate.areEqual(n, itr->second))
  {
    return;
  }
  Node on = itr->second;
  // otherwise infer they are equal
  Trace("nl-ff") << "*** Equal: " << n << " == " << on << ", both equal to "
                 << ns << std::endl;
  std::vector<Node> toProcess;
  toProcess.push_back(n);
  toProcess.push_back(on);
  std::unordered_set<Node> processed;
  std::vector<Node> exp;
  size_t i = 0;
  // expand
  while (i < toProcess.size())
  {
    Node v = toProcess[i];
    i++;
    if (!processed.insert(v).second)
    {
      continue;
    }
    if (v.getKind() == Kind::NONLINEAR_MULT)
    {
      toProcess.insert(toProcess.end(), v.begin(), v.end());
      continue;
    }
    // get the representative via arithmetic state, which note may be a
    // no-op if v is not in the equality engine.
    Node vr = d_astate.getRepresentative(v);
    itr = repEq.find(vr);
    if (itr != repEq.end() && itr->second != v)
    {
      exp.push_back(v.eqNode(itr->second));
      toProcess.push_back(itr->second);
    }
  }
  Trace("nl-ff") << "...explanation is " << exp << std::endl;
  NodeManager* nm = nodeManager();
  Node conc = on.eqNode(n);
  // double check that the substitution implies the conclusion is equal
  if (Configuration::isAssertionBuild())
  {
    ArithSubs as;
    for (const Node& e : exp)
    {
      ArithSubs asTmp;
      asTmp.add(e[0], e[1]);
      for (size_t j = 0, nums = as.d_subs.size(); j < nums; j++)
      {
        as.d_subs[j] = asTmp.applyArith(as.d_subs[j]);
      }
      as.append(asTmp);
    }
    Node concs1 = rewrite(as.applyArith(conc[0]));
    Node concs2 = rewrite(as.applyArith(conc[1]));
    Trace("nl-ff") << "Explaining substitution:" << std::endl;
    for (size_t j = 0, nums = as.d_subs.size(); j < nums; j++)
    {
      Trace("nl-ff") << "  " << as.d_vars[j] << " |-> " << as.d_subs[j]
                     << std::endl;
    }
    Assert(concs1 == concs2)
        << "...simplifies to " << concs1 << " and " << concs2;
  }
  Node lemf = nm->mkNode(Kind::IMPLIES, nm->mkAnd(exp), conc);
  NlLemma lem(InferenceId::ARITH_NL_FLATTEN_MON, lemf, LemmaProperty::NONE, d_pfgen.get());
  d_im.addPendingLemma(lem);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
