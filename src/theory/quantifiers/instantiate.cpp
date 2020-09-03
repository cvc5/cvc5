/*********************                                                        */
/*! \file instantiate.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiate
 **/

#include "theory/quantifiers/instantiate.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Instantiate::Instantiate(QuantifiersEngine* qe,
                         context::UserContext* u,
                         ProofNodeManager* pnm)
    : d_qe(qe),
      d_pnm(pnm),
      d_term_db(nullptr),
      d_term_util(nullptr),
      d_total_inst_debug(u),
      d_c_inst_match_trie_dom(u),
      d_pfInst(pnm ? new CDProof(pnm) : nullptr)
{
}

Instantiate::~Instantiate()
{
  for (std::pair<const Node, inst::CDInstMatchTrie*>& t : d_c_inst_match_trie)
  {
    delete t.second;
  }
  d_c_inst_match_trie.clear();
}

bool Instantiate::reset(Theory::Effort e)
{
  if (!d_recorded_inst.empty())
  {
    Trace("quant-engine-debug") << "Removing " << d_recorded_inst.size()
                                << " instantiations..." << std::endl;
    // remove explicitly recorded instantiations
    for (std::pair<Node, std::vector<Node> >& r : d_recorded_inst)
    {
      removeInstantiationInternal(r.first, r.second);
    }
    d_recorded_inst.clear();
  }
  d_term_db = d_qe->getTermDatabase();
  d_term_util = d_qe->getTermUtil();
  return true;
}

void Instantiate::registerQuantifier(Node q) {}
bool Instantiate::checkComplete()
{
  if (!d_recorded_inst.empty())
  {
    Trace("quant-engine-debug")
        << "Set incomplete due to recorded instantiations." << std::endl;
    return false;
  }
  return true;
}

void Instantiate::addRewriter(InstantiationRewriter* ir)
{
  d_instRewrite.push_back(ir);
}

bool Instantiate::addInstantiation(
    Node q, InstMatch& m, bool mkRep, bool modEq, bool doVts)
{
  Assert(q[0].getNumChildren() == m.d_vals.size());
  return addInstantiation(q, m.d_vals, mkRep, modEq, doVts);
}

bool Instantiate::addInstantiation(
    Node q, std::vector<Node>& terms, bool mkRep, bool modEq, bool doVts)
{
  // For resource-limiting (also does a time check).
  d_qe->getOutputChannel().safePoint(ResourceManager::Resource::QuantifierStep);
  Assert(!d_qe->inConflict());
  Assert(terms.size() == q[0].getNumChildren());
  Assert(d_term_db != nullptr);
  Assert(d_term_util != nullptr);
  Trace("inst-add-debug") << "For quantified formula " << q
                          << ", add instantiation: " << std::endl;
  for (unsigned i = 0, size = terms.size(); i < size; i++)
  {
    Trace("inst-add-debug") << "  " << q[0][i];
    Trace("inst-add-debug2") << " -> " << terms[i];
    TypeNode tn = q[0][i].getType();
    if (terms[i].isNull())
    {
      terms[i] = getTermForType(tn);
    }
    // Ensure the type is correct, this for instance ensures that real terms
    // are cast to integers for { x -> t } where x has type Int and t has
    // type Real.
    terms[i] = ensureType(terms[i], tn);
    if (mkRep)
    {
      // pick the best possible representative for instantiation, based on past
      // use and simplicity of term
      terms[i] = d_qe->getInternalRepresentative(terms[i], q, i);
    }
    Trace("inst-add-debug") << " -> " << terms[i] << std::endl;
    if (terms[i].isNull())
    {
      Trace("inst-add-debug")
          << " --> Failed to make term vector, due to term/type restrictions."
          << std::endl;
      return false;
    }
#ifdef CVC4_ASSERTIONS
    bool bad_inst = false;
    if (quantifiers::TermUtil::containsUninterpretedConstant(terms[i]))
    {
      Trace("inst") << "***& inst contains uninterpreted constant : "
                    << terms[i] << std::endl;
      bad_inst = true;
    }
    else if (!terms[i].getType().isSubtypeOf(q[0][i].getType()))
    {
      Trace("inst") << "***& inst bad type : " << terms[i] << " "
                    << terms[i].getType() << "/" << q[0][i].getType()
                    << std::endl;
      bad_inst = true;
    }
    else if (options::cegqi())
    {
      Node icf = quantifiers::TermUtil::getInstConstAttr(terms[i]);
      if (!icf.isNull())
      {
        if (icf == q)
        {
          Trace("inst") << "***& inst contains inst constant attr : "
                        << terms[i] << std::endl;
          bad_inst = true;
        }
        else if (expr::hasSubterm(terms[i], d_term_util->d_inst_constants[q]))
        {
          Trace("inst") << "***& inst contains inst constants : " << terms[i]
                        << std::endl;
          bad_inst = true;
        }
      }
    }
    // this assertion is critical to soundness
    if (bad_inst)
    {
      Trace("inst") << "***& Bad Instantiate " << q << " with " << std::endl;
      for (unsigned j = 0; j < terms.size(); j++)
      {
        Trace("inst") << "   " << terms[j] << std::endl;
      }
      Assert(false);
    }
#endif
  }

  // Note we check for entailment before checking for term vector duplication.
  // Although checking for term vector duplication is a faster check, it is
  // included automatically with recordInstantiationInternal, hence we prefer
  // two checks instead of three. In experiments, it is 1% slower or so to call
  // existsInstantiation here.
  // Alternatively, we could return an (index, trie node) in the call to
  // existsInstantiation here, where this would return the node in the trie
  // where we determined that there is definitely no duplication, and then
  // continue from that point in recordInstantiation below. However, for
  // simplicity, we do not pursue this option (as it would likely only
  // lead to very small gains).

  // check for positive entailment
  if (options::instNoEntail())
  {
    // should check consistency of equality engine
    // (if not aborting on utility's reset)
    std::map<TNode, TNode> subs;
    for (unsigned i = 0, size = terms.size(); i < size; i++)
    {
      subs[q[0][i]] = terms[i];
    }
    if (d_term_db->isEntailed(q[1], subs, false, true))
    {
      Trace("inst-add-debug") << " --> Currently entailed." << std::endl;
      ++(d_statistics.d_inst_duplicate_ent);
      return false;
    }
  }

  // check based on instantiation level
  if (options::instMaxLevel() != -1 || options::lteRestrictInstClosure())
  {
    for (Node& t : terms)
    {
      if (!d_term_db->isTermEligibleForInstantiation(t, q))
      {
        return false;
      }
    }
  }

  // record the instantiation
  bool recorded = recordInstantiationInternal(q, terms, modEq);
  if (!recorded)
  {
    Trace("inst-add-debug") << " --> Already exists (no record)." << std::endl;
    ++(d_statistics.d_inst_duplicate_eq);
    return false;
  }

  // Set up a proof if proofs are enabled. This proof stores a proof of
  // the instantiation body with q as a free assumption.
  std::shared_ptr<LazyCDProof> pfTmp;
  if (isProofEnabled())
  {
    pfTmp.reset(new LazyCDProof(
        d_pnm, nullptr, nullptr, "Instantiate::LazyCDProof::tmp"));
  }

  // construct the instantiation
  Trace("inst-add-debug") << "Constructing instantiation..." << std::endl;
  Assert(d_term_util->d_vars[q].size() == terms.size());
  // get the instantiation
  Node body =
      getInstantiation(q, d_term_util->d_vars[q], terms, doVts, pfTmp.get());
  Node orig_body = body;
  // now preprocess, storing the trust node for the rewrite
  TrustNode tpBody = quantifiers::QuantifiersRewriter::preprocess(body, true);
  if (!tpBody.isNull())
  {
    Assert(tpBody.getKind() == TrustNodeKind::REWRITE);
    body = tpBody.getNode();
    // do a tranformation step
    if (pfTmp != nullptr)
    {
      //              ----------------- from preprocess
      // orig_body    orig_body = body
      // ------------------------------ EQ_RESOLVE
      // body
      Node proven = tpBody.getProven();
      // add the transformation proof, or THEORY_PREPROCESS if none provided
      pfTmp->addLazyStep(proven,
                         tpBody.getGenerator(),
                         true,
                         "Instantiate::getInstantiation:qpreprocess",
                         false,
                         PfRule::THEORY_PREPROCESS);
      pfTmp->addStep(body, PfRule::EQ_RESOLVE, {orig_body, proven}, {body});
    }
  }
  Trace("inst-debug") << "...preprocess to " << body << std::endl;

  // construct the lemma
  Trace("inst-assert") << "(assert " << body << ")" << std::endl;

  // construct the instantiation, and rewrite the lemma
  Node lem = NodeManager::currentNM()->mkNode(kind::IMPLIES, q, body);

  // If proofs are enabled, construct the proof, which is of the form:
  // ... free assumption q ...
  // ------------------------- from pfTmp
  // body
  // ------------------------- SCOPE
  // (=> q body)
  // -------------------------- MACRO_SR_PRED_ELIM
  // lem
  bool hasProof = false;
  if (isProofEnabled())
  {
    // make the proof of body
    std::shared_ptr<ProofNode> pfn = pfTmp->getProofFor(body);
    // make the scope proof to get (=> q body)
    std::vector<Node> assumps;
    assumps.push_back(q);
    std::shared_ptr<ProofNode> pfns = d_pnm->mkScope({pfn}, assumps);
    Assert(assumps.size() == 1 && assumps[0] == q);
    // store in the main proof
    d_pfInst->addProof(pfns);
    Node prevLem = lem;
    lem = Rewriter::rewrite(lem);
    if (prevLem != lem)
    {
      d_pfInst->addStep(lem, PfRule::MACRO_SR_PRED_ELIM, {prevLem}, {});
    }
    hasProof = true;
  }
  else
  {
    lem = Rewriter::rewrite(lem);
  }

  // added lemma, which checks for lemma duplication
  bool addedLem = false;
  if (hasProof)
  {
    // use trust interface
    TrustNode tlem = TrustNode::mkTrustLemma(lem, d_pfInst.get());
    addedLem = d_qe->addTrustedLemma(tlem, true, false);
  }
  else
  {
    addedLem = d_qe->addLemma(lem, true, false);
  }

  if (!addedLem)
  {
    Trace("inst-add-debug") << " --> Lemma already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }

  d_total_inst_debug[q] = d_total_inst_debug[q] + 1;
  d_temp_inst_debug[q]++;
  if (Trace.isOn("inst"))
  {
    Trace("inst") << "*** Instantiate " << q << " with " << std::endl;
    for (unsigned i = 0, size = terms.size(); i < size; i++)
    {
      if (Trace.isOn("inst"))
      {
        Trace("inst") << "   " << terms[i];
        if (Trace.isOn("inst-debug"))
        {
          Trace("inst-debug") << ", type=" << terms[i].getType()
                              << ", var_type=" << q[0][i].getType();
        }
        Trace("inst") << std::endl;
      }
    }
  }
  if (options::instMaxLevel() != -1)
  {
    if (doVts)
    {
      // virtual term substitution/instantiation level features are
      // incompatible
      std::stringstream ss;
      ss << "Cannot combine instantiation strategies that require virtual term "
            "substitution with those that restrict instantiation levels";
      throw LogicException(ss.str());
    }
    else
    {
      uint64_t maxInstLevel = 0;
      for (const Node& tc : terms)
      {
        if (tc.hasAttribute(InstLevelAttribute())
            && tc.getAttribute(InstLevelAttribute()) > maxInstLevel)
        {
          maxInstLevel = tc.getAttribute(InstLevelAttribute());
        }
      }
      QuantAttributes::setInstantiationLevelAttr(
          orig_body, q[1], maxInstLevel + 1);
    }
  }
  if (options::trackInstLemmas())
  {
    if (options::incrementalSolving())
    {
      recorded = d_c_inst_match_trie[q]->recordInstLemma(q, terms, lem);
    }
    else
    {
      recorded = d_inst_match_trie[q].recordInstLemma(q, terms, lem);
    }
    Trace("inst-add-debug") << "...was recorded : " << recorded << std::endl;
    Assert(recorded);
  }
  Trace("inst-add-debug") << " --> Success." << std::endl;
  ++(d_statistics.d_instantiations);
  return true;
}

bool Instantiate::removeInstantiation(Node q,
                                      Node lem,
                                      std::vector<Node>& terms)
{
  // lem must occur in d_waiting_lemmas
  if (d_qe->removeLemma(lem))
  {
    return removeInstantiationInternal(q, terms);
  }
  return false;
}

bool Instantiate::recordInstantiation(Node q,
                                      std::vector<Node>& terms,
                                      bool modEq,
                                      bool addedLem)
{
  return recordInstantiationInternal(q, terms, modEq, addedLem);
}

bool Instantiate::existsInstantiation(Node q,
                                      std::vector<Node>& terms,
                                      bool modEq)
{
  if (options::incrementalSolving())
  {
    std::map<Node, inst::CDInstMatchTrie*>::iterator it =
        d_c_inst_match_trie.find(q);
    if (it != d_c_inst_match_trie.end())
    {
      return it->second->existsInstMatch(
          d_qe, q, terms, d_qe->getUserContext(), modEq);
    }
  }
  else
  {
    std::map<Node, inst::InstMatchTrie>::iterator it =
        d_inst_match_trie.find(q);
    if (it != d_inst_match_trie.end())
    {
      return it->second.existsInstMatch(d_qe, q, terms, modEq);
    }
  }
  return false;
}

Node Instantiate::getInstantiation(Node q,
                                   std::vector<Node>& vars,
                                   std::vector<Node>& terms,
                                   bool doVts,
                                   LazyCDProof* pf)
{
  Node body;
  Assert(vars.size() == terms.size());
  Assert(q[0].getNumChildren() == vars.size());
  // Notice that this could be optimized, but no significant performance
  // improvements were observed with alternative implementations (see #1386).
  body = q[1].substitute(vars.begin(), vars.end(), terms.begin(), terms.end());

  // store the proof of the instantiated body, with (open) assumption q
  if (pf != nullptr)
  {
    pf->addStep(body, PfRule::INSTANTIATE, {q}, terms);
  }

  // run rewriters to rewrite the instantiation in sequence.
  for (InstantiationRewriter*& ir : d_instRewrite)
  {
    TrustNode trn = ir->rewriteInstantiation(q, terms, body, doVts);
    if (!trn.isNull())
    {
      Node newBody = trn.getNode();
      // if using proofs, we store a preprocess + transformation step.
      if (pf != nullptr)
      {
        Node proven = trn.getProven();
        pf->addLazyStep(proven,
                        trn.getGenerator(),
                        true,
                        "Instantiate::getInstantiation:rewrite_inst",
                        false,
                        PfRule::THEORY_PREPROCESS);
        pf->addStep(newBody, PfRule::EQ_RESOLVE, {body, proven}, {});
      }
      body = newBody;
    }
  }
  return body;
}

Node Instantiate::getInstantiation(Node q, InstMatch& m, bool doVts)
{
  Assert(d_term_util->d_vars.find(q) != d_term_util->d_vars.end());
  Assert(m.d_vals.size() == q[0].getNumChildren());
  return getInstantiation(q, d_term_util->d_vars[q], m.d_vals, doVts);
}

Node Instantiate::getInstantiation(Node q, std::vector<Node>& terms, bool doVts)
{
  Assert(d_term_util->d_vars.find(q) != d_term_util->d_vars.end());
  return getInstantiation(q, d_term_util->d_vars[q], terms, doVts);
}

bool Instantiate::recordInstantiationInternal(Node q,
                                              std::vector<Node>& terms,
                                              bool modEq,
                                              bool addedLem)
{
  if (!addedLem)
  {
    // record the instantiation for deletion later
    d_recorded_inst.push_back(std::pair<Node, std::vector<Node> >(q, terms));
  }
  if (options::incrementalSolving())
  {
    Trace("inst-add-debug")
        << "Adding into context-dependent inst trie, modEq = " << modEq
        << std::endl;
    inst::CDInstMatchTrie* imt;
    std::map<Node, inst::CDInstMatchTrie*>::iterator it =
        d_c_inst_match_trie.find(q);
    if (it != d_c_inst_match_trie.end())
    {
      imt = it->second;
    }
    else
    {
      imt = new inst::CDInstMatchTrie(d_qe->getUserContext());
      d_c_inst_match_trie[q] = imt;
    }
    d_c_inst_match_trie_dom.insert(q);
    return imt->addInstMatch(d_qe, q, terms, d_qe->getUserContext(), modEq);
  }
  Trace("inst-add-debug") << "Adding into inst trie" << std::endl;
  return d_inst_match_trie[q].addInstMatch(d_qe, q, terms, modEq);
}

bool Instantiate::removeInstantiationInternal(Node q, std::vector<Node>& terms)
{
  if (options::incrementalSolving())
  {
    std::map<Node, inst::CDInstMatchTrie*>::iterator it =
        d_c_inst_match_trie.find(q);
    if (it != d_c_inst_match_trie.end())
    {
      return it->second->removeInstMatch(q, terms);
    }
    return false;
  }
  return d_inst_match_trie[q].removeInstMatch(q, terms);
}

Node Instantiate::getTermForType(TypeNode tn)
{
  if (tn.isClosedEnumerable())
  {
    return d_qe->getTermEnumeration()->getEnumerateTerm(tn, 0);
  }
  return d_qe->getTermDatabase()->getOrMakeTypeGroundTerm(tn);
}

bool Instantiate::printInstantiations(std::ostream& out)
{
  if (options::printInstMode() == options::PrintInstMode::NUM)
  {
    return printInstantiationsNum(out);
  }
  Assert(options::printInstMode() == options::PrintInstMode::LIST);
  return printInstantiationsList(out);
}

bool Instantiate::printInstantiationsList(std::ostream& out)
{
  bool useUnsatCore = false;
  std::vector<Node> active_lemmas;
  if (options::trackInstLemmas() && getUnsatCoreLemmas(active_lemmas))
  {
    useUnsatCore = true;
  }
  bool printed = false;
  bool isFull = options::printInstFull();
  if (options::incrementalSolving())
  {
    for (std::pair<const Node, inst::CDInstMatchTrie*>& t : d_c_inst_match_trie)
    {
      std::stringstream qout;
      if (!printQuant(t.first, qout, isFull))
      {
        continue;
      }
      std::stringstream sout;
      t.second->print(sout, t.first, useUnsatCore, active_lemmas);
      if (!sout.str().empty())
      {
        out << "(instantiations " << qout.str() << std::endl;
        out << sout.str();
        out << ")" << std::endl;
        printed = true;
      }
    }
  }
  else
  {
    for (std::pair<const Node, inst::InstMatchTrie>& t : d_inst_match_trie)
    {
      std::stringstream qout;
      if (!printQuant(t.first, qout, isFull))
      {
        continue;
      }
      std::stringstream sout;
      t.second.print(sout, t.first, useUnsatCore, active_lemmas);
      if (!sout.str().empty())
      {
        out << "(instantiations " << qout.str() << std::endl;
        out << sout.str();
        out << ")" << std::endl;
        printed = true;
      }
    }
  }
  return printed;
}

bool Instantiate::printInstantiationsNum(std::ostream& out)
{
  if (d_total_inst_debug.empty())
  {
    return false;
  }
  bool isFull = options::printInstFull();
  for (NodeUIntMap::iterator it = d_total_inst_debug.begin();
       it != d_total_inst_debug.end();
       ++it)
  {
    std::stringstream ss;
    if (printQuant((*it).first, ss, isFull))
    {
      out << "(num-instantiations " << ss.str() << " " << (*it).second << ")"
          << std::endl;
    }
  }
  return true;
}

bool Instantiate::printQuant(Node q, std::ostream& out, bool isFull)
{
  if (isFull)
  {
    out << q;
    return true;
  }
  quantifiers::QuantAttributes* qa = d_qe->getQuantAttributes();
  Node name = qa->getQuantName(q);
  if (name.isNull())
  {
    return false;
  }
  out << name;
  return true;
}

void Instantiate::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs)
{
  if (options::incrementalSolving())
  {
    for (context::CDHashSet<Node, NodeHashFunction>::const_iterator it =
             d_c_inst_match_trie_dom.begin();
         it != d_c_inst_match_trie_dom.end();
         ++it)
    {
      qs.push_back(*it);
    }
  }
  else
  {
    for (std::pair<const Node, inst::InstMatchTrie>& t : d_inst_match_trie)
    {
      qs.push_back(t.first);
    }
  }
}

bool Instantiate::getUnsatCoreLemmas(std::vector<Node>& active_lemmas)
{
  // only if unsat core available
  if (options::unsatCores())
  {
    if (!ProofManager::currentPM()->unsatCoreAvailable())
    {
      return false;
    }
  }
  else
  {
    return false;
  }

  Trace("inst-unsat-core") << "Get instantiations in unsat core..."
                           << std::endl;
  ProofManager::currentPM()->getLemmasInUnsatCore(active_lemmas);
  if (Trace.isOn("inst-unsat-core"))
  {
    Trace("inst-unsat-core") << "Quantifiers lemmas in unsat core: "
                             << std::endl;
    for (const Node& lem : active_lemmas)
    {
      Trace("inst-unsat-core") << "  " << lem << std::endl;
    }
    Trace("inst-unsat-core") << std::endl;
  }
  return true;
}

void Instantiate::getInstantiationTermVectors(
    Node q, std::vector<std::vector<Node> >& tvecs)
{
  std::vector<Node> lemmas;
  getInstantiations(q, lemmas);
  std::map<Node, Node> quant;
  std::map<Node, std::vector<Node> > tvec;
  getExplanationForInstLemmas(lemmas, quant, tvec);
  for (std::pair<const Node, std::vector<Node> >& t : tvec)
  {
    tvecs.push_back(t.second);
  }
}

void Instantiate::getInstantiationTermVectors(
    std::map<Node, std::vector<std::vector<Node> > >& insts)
{
  if (options::incrementalSolving())
  {
    for (std::pair<const Node, inst::CDInstMatchTrie*>& t : d_c_inst_match_trie)
    {
      getInstantiationTermVectors(t.first, insts[t.first]);
    }
  }
  else
  {
    for (std::pair<const Node, inst::InstMatchTrie>& t : d_inst_match_trie)
    {
      getInstantiationTermVectors(t.first, insts[t.first]);
    }
  }
}

void Instantiate::getExplanationForInstLemmas(
    const std::vector<Node>& lems,
    std::map<Node, Node>& quant,
    std::map<Node, std::vector<Node> >& tvec)
{
  if (!options::trackInstLemmas())
  {
    std::stringstream msg;
    msg << "Cannot get explanation for instantiations when --track-inst-lemmas "
           "is false.";
    throw OptionException(msg.str());
  }
  if (options::incrementalSolving())
  {
    for (std::pair<const Node, inst::CDInstMatchTrie*>& t : d_c_inst_match_trie)
    {
      t.second->getExplanationForInstLemmas(t.first, lems, quant, tvec);
    }
  }
  else
  {
    for (std::pair<const Node, inst::InstMatchTrie>& t : d_inst_match_trie)
    {
      t.second.getExplanationForInstLemmas(t.first, lems, quant, tvec);
    }
  }
#ifdef CVC4_ASSERTIONS
  for (unsigned j = 0; j < lems.size(); j++)
  {
    Assert(quant.find(lems[j]) != quant.end());
    Assert(tvec.find(lems[j]) != tvec.end());
  }
#endif
}

bool Instantiate::isProofEnabled() const { return d_pfInst != nullptr; }

void Instantiate::getInstantiations(std::map<Node, std::vector<Node> >& insts)
{
  if (!options::trackInstLemmas())
  {
    std::stringstream msg;
    msg << "Cannot get instantiations when --track-inst-lemmas is false.";
    throw OptionException(msg.str());
  }
  std::vector<Node> active_lemmas;
  bool useUnsatCore = getUnsatCoreLemmas(active_lemmas);

  if (options::incrementalSolving())
  {
    for (std::pair<const Node, inst::CDInstMatchTrie*>& t : d_c_inst_match_trie)
    {
      t.second->getInstantiations(
          insts[t.first], t.first, d_qe, useUnsatCore, active_lemmas);
    }
  }
  else
  {
    for (std::pair<const Node, inst::InstMatchTrie>& t : d_inst_match_trie)
    {
      t.second.getInstantiations(
          insts[t.first], t.first, d_qe, useUnsatCore, active_lemmas);
    }
  }
}

void Instantiate::getInstantiations(Node q, std::vector<Node>& insts)
{
  if (options::incrementalSolving())
  {
    std::map<Node, inst::CDInstMatchTrie*>::iterator it =
        d_c_inst_match_trie.find(q);
    if (it != d_c_inst_match_trie.end())
    {
      std::vector<Node> active_lemmas;
      it->second->getInstantiations(
          insts, it->first, d_qe, false, active_lemmas);
    }
  }
  else
  {
    std::map<Node, inst::InstMatchTrie>::iterator it =
        d_inst_match_trie.find(q);
    if (it != d_inst_match_trie.end())
    {
      std::vector<Node> active_lemmas;
      it->second.getInstantiations(
          insts, it->first, d_qe, false, active_lemmas);
    }
  }
}

Node Instantiate::getInstantiatedConjunction(Node q)
{
  Assert(q.getKind() == FORALL);
  std::vector<Node> insts;
  getInstantiations(q, insts);
  if (insts.empty())
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  Node ret;
  if (insts.size() == 1)
  {
    ret = insts[0];
  }
  else
  {
    ret = NodeManager::currentNM()->mkNode(kind::AND, insts);
  }
  // have to remove q
  // may want to do this in a better way
  TNode tq = q;
  TNode tt = NodeManager::currentNM()->mkConst(true);
  ret = ret.substitute(tq, tt);
  return ret;
}

void Instantiate::debugPrint(std::ostream& out)
{
  // debug information
  if (Trace.isOn("inst-per-quant-round"))
  {
    for (std::pair<const Node, uint32_t>& i : d_temp_inst_debug)
    {
      Trace("inst-per-quant-round") << " * " << i.second << " for " << i.first
                                    << std::endl;
      d_temp_inst_debug[i.first] = 0;
    }
  }
  if (options::debugInst())
  {
    bool isFull = options::printInstFull();
    for (std::pair<const Node, uint32_t>& i : d_temp_inst_debug)
    {
      std::stringstream ss;
      if (!printQuant(i.first, ss, isFull))
      {
        continue;
      }
      out << "(num-instantiations " << ss.str() << " " << i.second << ")"
          << std::endl;
    }
  }
}

void Instantiate::debugPrintModel()
{
  if (Trace.isOn("inst-per-quant"))
  {
    for (NodeUIntMap::iterator it = d_total_inst_debug.begin();
         it != d_total_inst_debug.end();
         ++it)
    {
      Trace("inst-per-quant")
          << " * " << (*it).second << " for " << (*it).first << std::endl;
    }
  }
}

Node Instantiate::ensureType(Node n, TypeNode tn)
{
  Trace("inst-add-debug2") << "Ensure " << n << " : " << tn << std::endl;
  TypeNode ntn = n.getType();
  Assert(ntn.isComparableTo(tn));
  if (ntn.isSubtypeOf(tn))
  {
    return n;
  }
  if (tn.isInteger())
  {
    return NodeManager::currentNM()->mkNode(TO_INTEGER, n);
  }
  return Node::null();
}

Instantiate::Statistics::Statistics()
    : d_instantiations("Instantiate::Instantiations_Total", 0),
      d_inst_duplicate("Instantiate::Duplicate_Inst", 0),
      d_inst_duplicate_eq("Instantiate::Duplicate_Inst_Eq", 0),
      d_inst_duplicate_ent("Instantiate::Duplicate_Inst_Entailed", 0)
{
  smtStatisticsRegistry()->registerStat(&d_instantiations);
  smtStatisticsRegistry()->registerStat(&d_inst_duplicate);
  smtStatisticsRegistry()->registerStat(&d_inst_duplicate_eq);
  smtStatisticsRegistry()->registerStat(&d_inst_duplicate_ent);
}

Instantiate::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_instantiations);
  smtStatisticsRegistry()->unregisterStat(&d_inst_duplicate);
  smtStatisticsRegistry()->unregisterStat(&d_inst_duplicate_eq);
  smtStatisticsRegistry()->unregisterStat(&d_inst_duplicate_ent);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
