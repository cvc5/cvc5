/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extended theory interface.
 *
 * This implements a generic module, used by theory solvers, for performing
 * "context-dependent simplification", as described in Reynolds et al
 * "Designing Theory Solvers with Extensions", FroCoS 2017.
 */

#include "theory/ext_theory.h"

#include "base/check.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"
#include "theory/output_channel.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"

using namespace std;

namespace cvc5::internal {
namespace theory {

const char* toString(ExtReducedId id)
{
  switch (id)
  {
    case ExtReducedId::NONE: return "NONE";
    case ExtReducedId::SR_CONST: return "SR_CONST";
    case ExtReducedId::REDUCTION: return "REDUCTION";
    case ExtReducedId::ARITH_SR_ZERO: return "ARITH_SR_ZERO";
    case ExtReducedId::ARITH_SR_LINEAR: return "ARITH_SR_LINEAR";
    case ExtReducedId::STRINGS_SR_CONST: return "STRINGS_SR_CONST";
    case ExtReducedId::STRINGS_NEG_CTN_DEQ: return "STRINGS_NEG_CTN_DEQ";
    case ExtReducedId::STRINGS_CTN_DECOMPOSE: return "STRINGS_CTN_DECOMPOSE";
    case ExtReducedId::STRINGS_REGEXP_INTER: return "STRINGS_REGEXP_INTER";
    case ExtReducedId::STRINGS_REGEXP_INTER_SUBSUME:
      return "STRINGS_REGEXP_INTER_SUBSUME";
    case ExtReducedId::STRINGS_REGEXP_INCLUDE: return "STRINGS_REGEXP_INCLUDE";
    case ExtReducedId::STRINGS_REGEXP_INCLUDE_NEG:
      return "STRINGS_REGEXP_INCLUDE_NEG";
    case ExtReducedId::STRINGS_REGEXP_RE_SYM_NF:
      return "STRINGS_REGEXP_RE_SYM_NF";
    case ExtReducedId::STRINGS_REGEXP_PDERIVATIVE:
      return "STRINGS_REGEXP_PDERIVATIVE";
    case ExtReducedId::STRINGS_NTH_REV: return "STRINGS_NTH_REV";
    case ExtReducedId::UNKNOWN: return "?";
    default: Unreachable(); return "?ExtReducedId?";
  }
}

std::ostream& operator<<(std::ostream& out, ExtReducedId id)
{
  out << toString(id);
  return out;
}

bool ExtTheoryCallback::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node> >& exp)
{
  return false;
}
bool ExtTheoryCallback::isExtfReduced(
    int effort, Node n, Node on, std::vector<Node>& exp, ExtReducedId& id)
{
  id = ExtReducedId::SR_CONST;
  return n.isConst();
}
bool ExtTheoryCallback::getReduction(int effort,
                                    Node n,
                                    Node& nr,
                                    bool& isSatDep)
{
  return false;
}

ExtTheory::ExtTheory(Env& env, ExtTheoryCallback& p, TheoryInferenceManager& im)
    : EnvObj(env),
      d_parent(p),
      d_im(im),
      d_ext_func_terms(context()),
      d_extfExtReducedIdMap(context()),
      d_ci_inactive(userContext()),
      d_has_extf(context()),
      d_lemmas(userContext())
{
  d_true = nodeManager()->mkConst(true);
}

// Gets all leaf terms in n.
std::vector<Node> ExtTheory::collectVars(Node n)
{
  std::vector<Node> vars;
  std::set<Node> visited;
  std::vector<Node> worklist;
  worklist.push_back(n);
  while (!worklist.empty())
  {
    Node current = worklist.back();
    worklist.pop_back();
    if (current.isConst() || visited.count(current) > 0)
    {
      continue;
    }
    visited.insert(current);
    // Treat terms not belonging to this theory as leaf
    // note : chould include terms not belonging to this theory
    // (commented below)
    if (current.getNumChildren() > 0)
    {
      worklist.insert(worklist.end(), current.begin(), current.end());
    }
    else
    {
      vars.push_back(current);
    }
  }
  return vars;
}

// do inferences
void ExtTheory::getSubstitutedTerms(int effort,
                                    const std::vector<Node>& terms,
                                    std::vector<Node>& sterms,
                                    std::vector<std::vector<Node> >& exp)
{
  Trace("extt-debug") << "getSubstitutedTerms for " << terms.size() << " / "
                      << d_ext_func_terms.size() << " extended functions."
                      << std::endl;
  if (!terms.empty())
  {
    // all variables we need to find a substitution for
    std::vector<Node> vars;
    std::vector<Node> sub;
    std::map<Node, std::vector<Node> > expc;
    for (const Node& n : terms)
    {
      // do substitution, rewrite
      std::map<Node, ExtfInfo>::iterator iti = d_extf_info.find(n);
      Assert(iti != d_extf_info.end());
      for (const Node& v : iti->second.d_vars)
      {
        if (std::find(vars.begin(), vars.end(), v) == vars.end())
        {
          vars.push_back(v);
        }
      }
    }
    bool useSubs = d_parent.getCurrentSubstitution(effort, vars, sub, expc);
    // get the current substitution for all variables
    Assert(!useSubs || vars.size() == sub.size());
    for (const Node& n : terms)
    {
      Node ns = n;
      std::vector<Node> expn;
      if (useSubs)
      {
        // do substitution
        ns = n.substitute(vars.begin(), vars.end(), sub.begin(), sub.end());
        if (ns != n)
        {
          // build explanation: explanation vars = sub for each vars in FV(n)
          std::map<Node, ExtfInfo>::iterator iti = d_extf_info.find(n);
          Assert(iti != d_extf_info.end());
          for (const Node& v : iti->second.d_vars)
          {
            std::map<Node, std::vector<Node> >::iterator itx = expc.find(v);
            if (itx != expc.end())
            {
              for (const Node& e : itx->second)
              {
                if (std::find(expn.begin(), expn.end(), e) == expn.end())
                {
                  expn.push_back(e);
                }
              }
            }
          }
        }
        Trace("extt-debug") << "  have " << n << " == " << ns
                            << ", exp size=" << expn.size() << "." << std::endl;
      }
      // add to vector
      sterms.push_back(ns);
      exp.push_back(expn);
    }
  }
}

bool ExtTheory::doInferencesInternal(int effort,
                                     const std::vector<Node>& terms,
                                     std::vector<Node>& nred)
{
  bool addedLemma = false;
  std::vector<Node> sterms;
  std::vector<std::vector<Node> > exp;
  getSubstitutedTerms(effort, terms, sterms, exp);
  NodeManager* nm = nodeManager();
  for (unsigned i = 0, size = terms.size(); i < size; i++)
  {
    bool processed = false;
    // if the substitution applied to terms[i] changed it
    if (sterms[i] != terms[i])
    {
      Node sr = rewrite(sterms[i]);
      // ask the theory if this term is reduced, e.g. is it constant or it
      // is a non-extf term.
      ExtReducedId id;
      if (d_parent.isExtfReduced(effort, sr, terms[i], exp[i], id))
      {
        processed = true;
        markInactive(terms[i], id);
        // We have exp[i] => terms[i] = sr
        Node eq = terms[i].eqNode(sr);
        Node lem = eq;
        if (!exp[i].empty())
        {
          Node antec = nm->mkAnd(exp[i]);
          lem = nm->mkNode(Kind::IMPLIES, antec, eq);
        }
        // will be able to generate a proof for this
        TrustNode trn = TrustNode::mkTrustLemma(lem, this);

        Trace("extt-debug") << "ExtTheory::doInferences : infer : " << eq
                            << " by " << exp[i] << std::endl;
        Trace("extt-debug") << "...send lemma " << lem << std::endl;
        if (sendLemma(trn, InferenceId::EXTT_SIMPLIFY))
        {
          Trace("extt-lemma")
              << "ExtTheory : substitution + rewrite lemma : " << lem
              << std::endl;
          addedLemma = true;
        }
      }
      else
      {
        // note : can add (non-reducing) lemma :
        //   exp[j] ^ exp[i] => sterms[i] = sterms[j]
        // if there are any duplicates, but we do not do this currently.
        Trace("extt-nred") << "Non-reduced term : " << sr << std::endl;
      }
    }
    else
    {
      Trace("extt-nred") << "Non-reduced term : " << sterms[i] << std::endl;
    }
    if (!processed)
    {
      nred.push_back(terms[i]);
    }
  }

  return addedLemma;
}

bool ExtTheory::sendLemma(TrustNode lem, InferenceId id)
{
  const Node& n = lem.getProven();
  if (d_lemmas.find(n) == d_lemmas.end())
  {
    if (d_im.trustedLemma(lem, id))
    {
      d_lemmas.insert(n);
      return true;
    }
  }
  return false;
}

bool ExtTheory::doInferences(int effort,
                             const std::vector<Node>& terms,
                             std::vector<Node>& nred)
{
  if (!terms.empty())
  {
    return doInferencesInternal(effort, terms, nred);
  }
  return false;
}

bool ExtTheory::doInferences(int effort, std::vector<Node>& nred)
{
  std::vector<Node> terms = getActive();
  return doInferencesInternal(effort, terms, nred);
}

// Register term.
void ExtTheory::registerTerm(Node n)
{
  if (d_extf_kind.find(n.getKind()) != d_extf_kind.end())
  {
    if (d_ext_func_terms.find(n) == d_ext_func_terms.end())
    {
      Trace("extt-debug") << "Found extended function : " << n << std::endl;
      d_ext_func_terms[n] = true;
      d_has_extf = n;
      d_extf_info[n].d_vars = collectVars(n);
    }
  }
}

// mark reduced
void ExtTheory::markInactive(Node n, ExtReducedId rid, bool satDep)
{
  Trace("extt-debug") << "Mark reduced " << n << std::endl;
  registerTerm(n);
  Assert(d_ext_func_terms.find(n) != d_ext_func_terms.end());
  d_ext_func_terms[n] = false;
  d_extfExtReducedIdMap[n] = rid;
  if (!satDep)
  {
    d_ci_inactive[n] = rid;
  }

  // update has_extf
  if (d_has_extf.get() == n)
  {
    for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
         it != d_ext_func_terms.end();
         ++it)
    {
      // if not already reduced
      if ((*it).second && !isContextIndependentInactive((*it).first))
      {
        d_has_extf = (*it).first;
      }
    }
  }
}

bool ExtTheory::isContextIndependentInactive(Node n) const
{
  ExtReducedId rid = ExtReducedId::UNKNOWN;
  return isContextIndependentInactive(n, rid);
}

bool ExtTheory::isContextIndependentInactive(Node n, ExtReducedId& rid) const
{
  NodeExtReducedIdMap::iterator it = d_ci_inactive.find(n);
  if (it != d_ci_inactive.end())
  {
    rid = it->second;
    return true;
  }
  return false;
}

void ExtTheory::getTerms(std::vector<Node>& terms)
{
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end();
       ++it)
  {
    terms.push_back((*it).first);
  }
}

bool ExtTheory::hasActiveTerm() const { return !d_has_extf.get().isNull(); }

bool ExtTheory::isActive(Node n) const
{
  ExtReducedId rid = ExtReducedId::UNKNOWN;
  return isActive(n, rid);
}

bool ExtTheory::isActive(Node n, ExtReducedId& rid) const
{
  NodeBoolMap::const_iterator it = d_ext_func_terms.find(n);
  if (it != d_ext_func_terms.end())
  {
    if ((*it).second)
    {
      return !isContextIndependentInactive(n, rid);
    }
    NodeExtReducedIdMap::const_iterator itr = d_extfExtReducedIdMap.find(n);
    Assert(itr != d_extfExtReducedIdMap.end());
    rid = itr->second;
    return false;
  }
  return false;
}

// get active
std::vector<Node> ExtTheory::getActive() const
{
  std::vector<Node> active;
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end();
       ++it)
  {
    // if not already reduced
    if ((*it).second && !isContextIndependentInactive((*it).first))
    {
      active.push_back((*it).first);
    }
  }
  return active;
}

std::vector<Node> ExtTheory::getActive(Kind k) const
{
  std::vector<Node> active;
  for (NodeBoolMap::iterator it = d_ext_func_terms.begin();
       it != d_ext_func_terms.end();
       ++it)
  {
    // if not already reduced
    if ((*it).first.getKind() == k && (*it).second
        && !isContextIndependentInactive((*it).first))
    {
      active.push_back((*it).first);
    }
  }
  return active;
}

std::shared_ptr<ProofNode> ExtTheory::getProofFor(Node fact)
{
  CDProof proof(d_env);
  std::vector<Node> antec;
  Node conc = fact;
  if (conc.getKind() == Kind::IMPLIES)
  {
    if (conc[0].getKind() == Kind::AND)
    {
      antec.insert(antec.end(), conc[0].begin(), conc[0].end());
    }
    else
    {
      antec.push_back(conc[0]);
    }
    conc = conc[1];
  }
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node res =
      pc->checkDebug(ProofRule::MACRO_SR_PRED_INTRO, antec, {conc}, conc);
  if (res.isNull())
  {
    Assert(false) << "ExtTheory failed to prove " << fact;
    return nullptr;
  }
  proof.addStep(conc, ProofRule::MACRO_SR_PRED_INTRO, antec, {conc});
  if (!antec.empty())
  {
    proof.addStep(fact, ProofRule::SCOPE, {conc}, antec);
  }
  // t1 = s1 ... tn = sn
  // -------------------- MACRO_SR_PRED_INTRO {t}
  // t = s
  // ----------------------------------- SCOPE {t1 = s1 ... tn = sn}
  // (t1 = s1 ^ ... ^ tn = sn) => (t = s).
  return proof.getProofFor(fact);
}

std::string ExtTheory::identify() const { return "ExtTheory"; }

}  // namespace theory
}  // namespace cvc5::internal
