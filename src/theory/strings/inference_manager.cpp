/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the inference manager for the theory of strings.
 */

#include "theory/strings/inference_manager.h"

#include "options/strings_options.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

InferenceManager::InferenceManager(Env& env,
                                   Theory& t,
                                   SolverState& s,
                                   TermRegistry& tr,
                                   ExtTheory& e,
                                   SequencesStatistics& statistics)
    : InferenceManagerBuffered(env, t, s, "theory::strings::"),
      d_state(s),
      d_termReg(tr),
      d_extt(e),
      d_statistics(statistics),
      d_ipc(isProofEnabled() ? new InferProofCons(env, context(), d_statistics)
                             : nullptr),
      d_ipcl(isProofEnabled() ? new InferProofCons(env, context(), d_statistics)
                              : nullptr)
{
  NodeManager* nm = NodeManager::currentNM();
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void InferenceManager::doPending()
{
  doPendingFacts();
  if (d_state.isInConflict())
  {
    // just clear the pending vectors, nothing else to do
    clearPendingLemmas();
    clearPendingPhaseRequirements();
    return;
  }
  doPendingLemmas();
  doPendingPhaseRequirements();
}

bool InferenceManager::sendInternalInference(std::vector<Node>& exp,
                                             Node conc,
                                             InferenceId infer)
{
  if (conc.getKind() == AND
      || (conc.getKind() == NOT && conc[0].getKind() == OR))
  {
    Node conj = conc.getKind() == AND ? conc : conc[0];
    bool pol = conc.getKind() == AND;
    bool ret = true;
    for (const Node& cc : conj)
    {
      bool retc = sendInternalInference(exp, pol ? cc : cc.negate(), infer);
      ret = ret && retc;
    }
    return ret;
  }
  bool pol = conc.getKind() != NOT;
  Node lit = pol ? conc : conc[0];
  if (lit.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (!lit[i].isConst() && !d_state.hasTerm(lit[i]))
      {
        // introduces a new non-constant term, do not infer
        return false;
      }
    }
    // does it already hold?
    if (pol ? d_state.areEqual(lit[0], lit[1])
            : d_state.areDisequal(lit[0], lit[1]))
    {
      return true;
    }
  }
  else if (lit.isConst())
  {
    if (lit.getConst<bool>())
    {
      Assert(pol);
      // trivially holds
      return true;
    }
  }
  else if (!d_state.hasTerm(lit))
  {
    // introduces a new non-constant term, do not infer
    return false;
  }
  else if (d_state.areEqual(lit, pol ? d_true : d_false))
  {
    // already holds
    return true;
  }
  sendInference(exp, conc, infer);
  return true;
}

bool InferenceManager::sendInference(const std::vector<Node>& exp,
                                     const std::vector<Node>& noExplain,
                                     Node eq,
                                     InferenceId infer,
                                     bool isRev,
                                     bool asLemma)
{
  if (eq.isNull())
  {
    eq = d_false;
  }
  else if (rewrite(eq) == d_true)
  {
    // if trivial, return
    return false;
  }
  // wrap in infer info and send below
  InferInfo ii(infer);
  ii.d_idRev = isRev;
  ii.d_conc = eq;
  ii.d_premises = exp;
  ii.d_noExplain = noExplain;
  sendInference(ii, asLemma);
  return true;
}

bool InferenceManager::sendInference(const std::vector<Node>& exp,
                                     Node eq,
                                     InferenceId infer,
                                     bool isRev,
                                     bool asLemma)
{
  std::vector<Node> noExplain;
  return sendInference(exp, noExplain, eq, infer, isRev, asLemma);
}

void InferenceManager::sendInference(InferInfo& ii, bool asLemma)
{
  Assert(!ii.isTrivial());
  // set that this inference manager will be processing this inference
  ii.d_sim = this;
  Trace("strings-infer-debug")
      << "sendInference: " << ii << ", asLemma = " << asLemma << std::endl;
  // check if we should send a conflict, lemma or a fact
  if (ii.isConflict())
  {
    Trace("strings-infer-debug") << "...as conflict" << std::endl;
    Trace("strings-lemma") << "Strings::Conflict: " << ii.d_premises << " by "
                           << ii.getId() << std::endl;
    Trace("strings-conflict") << "CONFLICT: inference conflict " << ii.d_premises << " by " << ii.getId() << std::endl;
    ++(d_statistics.d_conflictsInfer);
    // process the conflict immediately
    processConflict(ii);
    return;
  }
  else if (asLemma || options().strings.stringInferAsLemmas || !ii.isFact())
  {
    Trace("strings-infer-debug") << "...as lemma" << std::endl;
    addPendingLemma(std::unique_ptr<InferInfo>(new InferInfo(ii)));
    return;
  }
  if (options().strings.stringInferSym)
  {
    std::vector<Node> unproc;
    for (const Node& ac : ii.d_premises)
    {
      d_termReg.removeProxyEqs(ac, unproc);
    }
    if (unproc.empty())
    {
      Node eqs = ii.d_conc;
      // keep the same id for now, since we are transforming the form of the
      // inference, not the root reason.
      InferInfo iiSubsLem(ii.getId());
      iiSubsLem.d_sim = this;
      iiSubsLem.d_conc = eqs;
      if (TraceIsOn("strings-lemma-debug"))
      {
        Trace("strings-lemma-debug")
            << "Strings::Infer " << iiSubsLem << std::endl;
        Trace("strings-lemma-debug")
            << "Strings::Infer Alternate : " << eqs << std::endl;
      }
      Trace("strings-infer-debug") << "...as symbolic lemma" << std::endl;
      addPendingLemma(std::unique_ptr<InferInfo>(new InferInfo(iiSubsLem)));
      return;
    }
    if (TraceIsOn("strings-lemma-debug"))
    {
      for (const Node& u : unproc)
      {
        Trace("strings-lemma-debug")
            << "  non-trivial explanation : " << u << std::endl;
      }
    }
  }
  Trace("strings-infer-debug") << "...as fact" << std::endl;
  // add to pending to be processed as a fact
  addPendingFact(std::unique_ptr<InferInfo>(new InferInfo(ii)));
}

bool InferenceManager::sendSplit(Node a, Node b, InferenceId infer, bool preq)
{
  Node eq = a.eqNode(b);
  eq = rewrite(eq);
  if (eq.isConst())
  {
    return false;
  }
  NodeManager* nm = NodeManager::currentNM();
  InferInfo iiSplit(infer);
  iiSplit.d_sim = this;
  iiSplit.d_conc = nm->mkNode(OR, eq, nm->mkNode(NOT, eq));
  addPendingPhaseRequirement(eq, preq);
  addPendingLemma(std::unique_ptr<InferInfo>(new InferInfo(iiSplit)));
  return true;
}

void InferenceManager::addToExplanation(Node a,
                                        Node b,
                                        std::vector<Node>& exp) const
{
  if (a != b)
  {
    Trace("strings-explain")
        << "Add to explanation : " << a << " == " << b << std::endl;
    Assert(d_state.areEqual(a, b));
    exp.push_back(a.eqNode(b));
  }
}

void InferenceManager::addToExplanation(Node lit, std::vector<Node>& exp) const
{
  if (!lit.isNull())
  {
    Assert(!lit.isConst());
    exp.push_back(lit);
  }
}

bool InferenceManager::hasProcessed() const
{
  return d_state.isInConflict() || hasPending();
}

void InferenceManager::markInactive(Node n, ExtReducedId id, bool contextDepend)
{
  d_extt.markInactive(n, id, contextDepend);
}

void InferenceManager::processConflict(const InferInfo& ii)
{
  Assert(!d_state.isInConflict());
  if (ii.getId() == InferenceId::STRINGS_PREFIX_CONFLICT)
  {
    bool isSuf = ii.d_idRev;
    // The shape of prefix conflicts is P1? ^ P2? ^ (= x y)?
    // where if applicable:
    //   P1 implies a prefix on string x,
    //   P2 implies a (conflicting) prefix on string y.
    // See EqcInfo::mkMergeConflict.
    Trace("strings-prefix-min") << "Minimize prefix conflict " << ii.d_premises
                                << ", isSuf=" << isSuf << std::endl;
    size_t npremises = ii.d_premises.size();
    Node eq = ii.d_premises[npremises - 1];
    // if we included an equality, we will try to minimize its explanation
    if (eq.getKind() == EQUAL)
    {
      InferInfo iim(InferenceId::STRINGS_PREFIX_CONFLICT_MIN);
      Node pft[2] = {eq[0], eq[1]};
      for (size_t i = 0; i < (npremises - 1); i++)
      {
        if (ii.d_premises[i].getKind() == STRING_IN_REGEXP)
        {
          size_t eindex = ii.d_premises[i][0] == eq[0] ? 0 : 1;
          Assert(ii.d_premises[i][0] == eq[eindex]);
          // the basis of prefix for eq[eindex] is the RE of this premise
          pft[eindex] = ii.d_premises[i][1];
        }
        // include it in the explanation
        iim.d_premises.push_back(ii.d_premises[i]);
      }
      Trace("strings-prefix-min")
          << "Prefix terms: " << pft[0] << " / " << pft[1] << std::endl;
      Node pfv[2];
      for (size_t i = 0; i < 2; i++)
      {
        pfv[i] = utils::getConstantEndpoint(pft[i], isSuf);
      }
      Trace("strings-prefix-min")
          << "Prefixes: " << pfv[0] << " / " << pfv[1] << std::endl;
      for (size_t i = 0; i < 2; i++)
      {
        if (pft[1 - i] == eq[1 - i] && pft[i] != eq[i])
        {
          // if the other side is justified by itself and we are justified
          // externally, we can try to minimize the explanation of this
          // get the minimal conflicting prefix
          std::vector<TNode> assumptions;
          explain(eq, assumptions);
          std::map<TNode, TNode> emap = getExplanationMap(assumptions);
          Node mexp =
              mkPrefixExplainMin(eq[i], pfv[i], assumptions, emap, isSuf);
          // if we minimized the conflict, process it
          if (!mexp.isNull())
          {
            // must flatten here
            utils::flattenOp(AND, mexp, iim.d_premises);
            iim.d_conc = ii.d_conc;
            processConflict(iim);
            return;
          }
        }
      }
    }
    // otherwise if we fail to minimize, process the original
  }
  // setup the fact to reproduce the proof in the call below
  if (d_ipcl != nullptr)
  {
    d_ipcl->notifyLemma(ii);
  }
  // make the trust node
  TrustNode tconf = mkConflictExp(ii.d_premises, d_ipcl.get());
  Assert(tconf.getKind() == TrustNodeKind::CONFLICT);
  Trace("strings-assert") << "(assert (not " << tconf.getNode()
                          << ")) ; conflict " << ii.getId() << std::endl;
  // send the trusted conflict
  trustedConflict(tconf, ii.getId());
}

void InferenceManager::processFact(InferInfo& ii, ProofGenerator*& pg)
{
  Trace("strings-assert") << "(assert (=> " << ii.getPremises() << " "
                          << ii.d_conc << ")) ; fact " << ii.getId() << std::endl;
  Trace("strings-lemma") << "Strings::Fact: " << ii.d_conc << " from "
                         << ii.getPremises() << " by " << ii.getId()
                         << std::endl;
  if (d_ipc != nullptr)
  {
    // ensure the proof generator is ready to explain this fact in the
    // current SAT context
    d_ipc->notifyFact(ii);
    pg = d_ipc.get();
  }
  // ensure facts are for rewritten terms
  if (Configuration::isAssertionBuild())
  {
    Node atom = ii.d_conc.getKind()==NOT ? ii.d_conc[0] : ii.d_conc;
    if (atom.getKind()==EQUAL)
    {
      Assert(rewrite(atom[0])==atom[0]);
      Assert(rewrite(atom[1])==atom[1]);
    }
    else
    {
      Assert(rewrite(atom)==atom);
    }
  }
}

TrustNode InferenceManager::processLemma(InferInfo& ii, LemmaProperty& p)
{
  Assert(!ii.isTrivial());
  Assert(!ii.isConflict());
  // set up the explanation and no-explanation
  std::vector<Node> exp;
  for (const Node& ec : ii.d_premises)
  {
    utils::flattenOp(AND, ec, exp);
  }
  std::vector<Node> noExplain;
  if (!options().strings.stringRExplainLemmas)
  {
    // if we aren't regressing the explanation, we add all literals to
    // noExplain and ignore ii.d_ant.
    noExplain.insert(noExplain.end(), exp.begin(), exp.end());
  }
  else
  {
    // otherwise, the no-explain literals are those provided
    for (const Node& ecn : ii.d_noExplain)
    {
      utils::flattenOp(AND, ecn, noExplain);
    }
  }
  // ensure that the proof generator is ready to explain the final conclusion
  // of the lemma (ii.d_conc).
  if (d_ipcl != nullptr)
  {
    d_ipcl->notifyLemma(ii);
  }
  TrustNode tlem = mkLemmaExp(ii.d_conc, exp, noExplain, d_ipcl.get());
  Trace("strings-pending") << "Process pending lemma : " << tlem.getNode()
                           << std::endl;

  // Process the side effects of the inference info.
  // Register the new skolems from this inference. We register them here
  // (lazily), since this is the moment when we have decided to process the
  // inference.
  for (const std::pair<const LengthStatus, std::vector<Node> >& sks :
       ii.d_skolems)
  {
    for (const Node& n : sks.second)
    {
      d_termReg.registerTermAtomic(n, sks.first);
    }
  }
  if (ii.getId() == InferenceId::STRINGS_REDUCTION)
  {
    p |= LemmaProperty::NEEDS_JUSTIFY;
  }
  // send phase requirements
  for (const std::pair<const Node, bool>& pp : ii.d_pendingPhase)
  {
    Node ppr = rewrite(pp.first);
    addPendingPhaseRequirement(ppr, pp.second);
  }
  Trace("strings-assert") << "(assert " << tlem.getNode() << ") ; lemma "
                          << ii.getId() << std::endl;
  Trace("strings-lemma") << "Strings::Lemma: " << tlem.getNode() << " by "
                         << ii.getId() << std::endl;
  return tlem;
}

std::map<TNode, TNode> InferenceManager::getExplanationMap(
    const std::vector<TNode>& assumptions)
{
  std::map<TNode, TNode> emap;
  for (TNode e : assumptions)
  {
    if (e.getKind() != EQUAL)
    {
      // skip non-equalities, which could be included if we internally
      // concluded an equality as a fact from a non-equality
      continue;
    }
    for (size_t i = 0; i < 2; i++)
    {
      emap[e[i]] = e;
    }
  }
  return emap;
}
Node InferenceManager::mkPrefixExplainMin(Node x,
                                          Node prefix,
                                          const std::vector<TNode>& assumptions,
                                          const std::map<TNode, TNode>& emap,
                                          bool isSuf)
{
  Assert(prefix.isConst());
  Trace("strings-prefix-min")
      << "mkPrefixExplainMin: " << x << " for " << (isSuf ? "suffix" : "prefix")
      << " " << prefix << std::endl;
  Trace("strings-prefix-min") << "- via: " << assumptions << std::endl;
  std::vector<TNode> minAssumptions;
  // the current node(s) we are looking at
  std::vector<TNode> cc;
  cc.push_back(x);
  size_t pindex = 0;
  std::vector<Node> pchars = Word::getChars(prefix);
  std::map<TNode, TNode>::const_iterator it;
  bool isConflict = false;
  while (pindex < pchars.size() && !cc.empty())
  {
    Trace("strings-prefix-min")
        << "  " << pindex << "/" << pchars.size() << ", " << cc << std::endl;
    TNode c = cc.back();
    cc.pop_back();
    if (c.isConst())
    {
      // check for conflict
      std::vector<Node> cchars = Word::getChars(c);
      size_t cindex = 0;
      while (pindex < pchars.size() && cindex < cchars.size())
      {
        size_t pii = isSuf ? (pchars.size() - 1) - pindex : pindex;
        size_t cii = isSuf ? (cchars.size() - 1) - cindex : cindex;
        if (cchars[cii] != pchars[pii])
        {
          Trace("strings-prefix-min") << "...conflict at " << pindex
                                      << " while processing " << c << std::endl;
          isConflict = true;
          break;
        }
        pindex++;
        cindex++;
      }
      if (isConflict)
      {
        break;
      }
      continue;
    }
    it = emap.find(c);
    if (it != emap.end())
    {
      TNode ceq = it->second;
      // do not continue if not already processed, which also avoids
      // non-termination
      if (std::find(minAssumptions.begin(), minAssumptions.end(), ceq)
          == minAssumptions.end())
      {
        Assert(ceq.getKind() == EQUAL);
        Assert(ceq[0] == c || ceq[1] == c);
        // add to explanation and look at the term it is equal to
        minAssumptions.push_back(ceq);
        TNode oc = ceq[ceq[0] == c ? 1 : 0];
        cc.push_back(oc);
        continue;
      }
    }
    // we don't know what it is equal to
    // if it is a concatenation, try to recurse into children
    if (c.getKind() == STRING_CONCAT)
    {
      for (size_t i = 0, nchild = c.getNumChildren(); i < nchild; i++)
      {
        // reverse if it is a prefix
        size_t ii = isSuf ? i : (nchild - 1) - i;
        cc.push_back(c[ii]);
      }
      continue;
    }
    Trace("strings-prefix-min") << "-> no explanation for " << c << std::endl;
    break;
  }
  if (isConflict && minAssumptions.size() < assumptions.size())
  {
    Trace("strings-prefix-min")
        << "-> min-explained: " << minAssumptions << std::endl;
    Trace("strings-exp-min-stats")
        << "Min-explain (prefix) " << minAssumptions.size() << " / "
        << assumptions.size() << std::endl;
    return NodeManager::currentNM()->mkAnd(minAssumptions);
  }
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
