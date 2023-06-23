/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of instantiate.
 */

#include "theory/quantifiers/instantiate.h"

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node_manager.h"
#include "smt/logic_exception.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/entailment_check.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_preprocess.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Instantiate::Instantiate(Env& env,
                         QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         QuantifiersRegistry& qr,
                         TermRegistry& tr)
    : QuantifiersUtil(env),
      d_statistics(statisticsRegistry()),
      d_qstate(qs),
      d_qim(qim),
      d_qreg(qr),
      d_treg(tr),
      d_insts(userContext()),
      d_c_inst_match_trie_dom(userContext()),
      d_pfInst(isProofEnabled()
                   ? new CDProof(env, userContext(), "Instantiate::pfInst")
                   : nullptr)
{
}

Instantiate::~Instantiate()
{
  for (std::pair<const Node, CDInstMatchTrie*>& t : d_c_inst_match_trie)
  {
    delete t.second;
  }
  d_c_inst_match_trie.clear();
}

bool Instantiate::reset(Theory::Effort e)
{
  Trace("inst-debug") << "Reset, effort " << e << std::endl;
  // clear explicitly recorded instantiations
  d_recordedInst.clear();
  d_instDebugTemp.clear();
  return true;
}

void Instantiate::registerQuantifier(Node q) {}
bool Instantiate::checkComplete(IncompleteId& incId)
{
  if (!d_recordedInst.empty())
  {
    Trace("quant-engine-debug")
        << "Set incomplete due to recorded instantiations." << std::endl;
    incId = IncompleteId::QUANTIFIERS_RECORDED_INST;
    return false;
  }
  return true;
}

void Instantiate::addRewriter(InstantiationRewriter* ir)
{
  d_instRewrite.push_back(ir);
}

bool Instantiate::addInstantiation(Node q,
                                   std::vector<Node>& terms,
                                   InferenceId id,
                                   Node pfArg,
                                   bool doVts)
{
  // do the instantiation
  bool ret = addInstantiationInternal(q, terms, id, pfArg, doVts);
  // process the instantiation with callbacks via term registry
  d_treg.processInstantiation(q, terms, ret);
  // return whether the instantiation was successful
  return ret;
}

bool Instantiate::addInstantiationInternal(
    Node q, std::vector<Node>& terms, InferenceId id, Node pfArg, bool doVts)
{
  // For resource-limiting (also does a time check).
  d_qim.safePoint(Resource::QuantifierStep);
  Assert(!d_qstate.isInConflict());
  Assert(q.getKind() == FORALL);
  Assert(terms.size() == q[0].getNumChildren());
  if (TraceIsOn("inst-add-debug"))
  {
    Trace("inst-add-debug") << "For quantified formula " << q
                            << ", add instantiation: " << std::endl;
    for (size_t i = 0, size = terms.size(); i < size; i++)
    {
      Trace("inst-add-debug") << "  " << q[0][i];
      Trace("inst-add-debug") << " -> " << terms[i];
      Trace("inst-add-debug") << std::endl;
    }
    Trace("inst-add-debug") << "id is " << id << std::endl;
    Trace("inst-add-debug") << "doVts is " << doVts << std::endl;
  }
  // ensure the terms are non-null and well-typed
  for (size_t i = 0, size = terms.size(); i < size; i++)
  {
    TypeNode tn = q[0][i].getType();
    if (terms[i].isNull())
    {
      terms[i] = d_treg.getTermForType(tn);
    }
    // Ensure the type is correct, this for instance ensures that real terms
    // are cast to integers for { x -> t } where x has type Int and t has
    // type Real.
    terms[i] = ensureType(terms[i], tn);
    if (terms[i].isNull())
    {
      Trace("inst-add-debug")
          << " --> Failed to make term vector, due to term/type restrictions."
          << std::endl;
      return false;
    }
  }
#ifdef CVC5_ASSERTIONS
  for (size_t i = 0, size = terms.size(); i < size; i++)
  {
    TypeNode tn = q[0][i].getType();
    Assert(!terms[i].isNull());
    bool bad_inst = false;
    if (TermUtil::containsUninterpretedConstant(terms[i]))
    {
      Trace("inst") << "***& inst contains uninterpreted constant : "
                    << terms[i] << std::endl;
      bad_inst = true;
    }
    else if (terms[i].getType() != q[0][i].getType())
    {
      Trace("inst") << "***& inst bad type : " << terms[i] << " "
                    << terms[i].getType() << "/" << q[0][i].getType()
                    << std::endl;
      bad_inst = true;
    }
    else if (options().quantifiers.cegqi)
    {
      Node icf = TermUtil::getInstConstAttr(terms[i]);
      if (!icf.isNull())
      {
        if (icf == q)
        {
          Trace("inst") << "***& inst contains inst constant attr : "
                        << terms[i] << std::endl;
          bad_inst = true;
        }
        else if (expr::hasSubterm(terms[i], d_qreg.d_inst_constants[q]))
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
  }
#endif

  EntailmentCheck* ec = d_treg.getEntailmentCheck();
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
  if (options().quantifiers.instNoEntail)
  {
    // should check consistency of equality engine
    // (if not aborting on utility's reset)
    std::map<TNode, TNode> subs;
    for (unsigned i = 0, size = terms.size(); i < size; i++)
    {
      subs[q[0][i]] = terms[i];
    }
    if (ec->isEntailed(q[1], subs, false, true))
    {
      Trace("inst-add-debug") << " --> Currently entailed." << std::endl;
      ++(d_statistics.d_inst_duplicate_ent);
      return false;
    }
  }

  // check based on instantiation level
  if (options().quantifiers.instMaxLevel != -1)
  {
    TermDb* tdb = d_treg.getTermDatabase();
    for (const Node& t : terms)
    {
      if (!tdb->isTermEligibleForInstantiation(t, q))
      {
        return false;
      }
    }
  }

  // record the instantiation
  bool recorded = recordInstantiationInternal(q, terms);
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
        d_env, nullptr, nullptr, "Instantiate::LazyCDProof::tmp"));
  }

  // construct the instantiation
  Trace("inst-add-debug") << "Constructing instantiation..." << std::endl;
  Assert(d_qreg.d_vars[q].size() == terms.size());
  // get the instantiation
  Node body = getInstantiation(
      q, d_qreg.d_vars[q], terms, id, pfArg, doVts, pfTmp.get());
  Node orig_body = body;
  // now preprocess, storing the trust node for the rewrite
  TrustNode tpBody = d_qreg.getPreprocess().preprocess(body, true);
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
      // add the transformation proof, or the trusted rule if none provided
      pfTmp->addLazyStep(proven,
                         tpBody.getGenerator(),
                         PfRule::QUANTIFIERS_PREPROCESS,
                         true,
                         "Instantiate::getInstantiation:qpreprocess");
      pfTmp->addStep(body, PfRule::EQ_RESOLVE, {orig_body, proven}, {});
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
    std::shared_ptr<ProofNode> pfns =
        d_env.getProofNodeManager()->mkScope({pfn}, assumps);
    Assert(assumps.size() == 1 && assumps[0] == q);
    // store in the main proof
    d_pfInst->addProof(pfns);
    Node prevLem = lem;
    lem = rewrite(lem);
    if (prevLem != lem)
    {
      d_pfInst->addStep(lem, PfRule::MACRO_SR_PRED_ELIM, {prevLem}, {});
    }
    hasProof = true;
  }
  else
  {
    lem = rewrite(lem);
  }

  // added lemma, which checks for lemma duplication
  bool addedLem = false;
  if (hasProof)
  {
    // use proof generator
    addedLem =
        d_qim.addPendingLemma(lem, id, LemmaProperty::NONE, d_pfInst.get());
  }
  else
  {
    addedLem = d_qim.addPendingLemma(lem, id);
  }

  if (!addedLem)
  {
    Trace("inst-add-debug") << " --> Lemma already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }

  // add to list of instantiations
  InstLemmaList* ill = getOrMkInstLemmaList(q);
  ill->d_list.push_back(body);
  // add to temporary debug statistics (# inst on this round)
  d_instDebugTemp[q]++;
  if (TraceIsOn("inst"))
  {
    Trace("inst") << "*** Instantiate " << q << " with " << std::endl;
    for (size_t i = 0, size = terms.size(); i < size; i++)
    {
      if (TraceIsOn("inst"))
      {
        Trace("inst") << "   " << terms[i];
        if (TraceIsOn("inst-debug"))
        {
          Trace("inst-debug") << ", type=" << terms[i].getType()
                              << ", var_type=" << q[0][i].getType();
        }
        Trace("inst") << std::endl;
      }
    }
  }
  if (options().quantifiers.instMaxLevel != -1)
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
  Trace("inst-add-debug") << " --> Success." << std::endl;
  ++(d_statistics.d_instantiations);
  return true;
}

void Instantiate::processInstantiationRep(Node q, std::vector<Node>& terms)
{
  Assert(q.getKind() == FORALL);
  Assert(terms.size() == q[0].getNumChildren());
  for (size_t i = 0, size = terms.size(); i < size; i++)
  {
    Assert(!terms[i].isNull());
    // pick the best possible representative for instantiation, based on past
    // use and simplicity of term
    terms[i] = d_treg.getModel()->getInternalRepresentative(terms[i], q, i);
    // Note it may be a null representative here, it is then replaced
    // by an arbitrary term if necessary during addInstantiation.
  }
}

bool Instantiate::addInstantiationExpFail(Node q,
                                          std::vector<Node>& terms,
                                          std::vector<bool>& failMask,
                                          InferenceId id,
                                          Node pfArg,
                                          bool doVts,
                                          bool expFull)
{
  if (addInstantiation(q, terms, id, pfArg, doVts))
  {
    return true;
  }
  size_t tsize = terms.size();
  failMask.resize(tsize, true);
  if (tsize == 1)
  {
    // will never succeed with 1 variable
    return false;
  }
  EntailmentCheck* echeck = d_treg.getEntailmentCheck();
  Trace("inst-exp-fail") << "Explain inst failure..." << terms << std::endl;
  // set up information for below
  std::vector<Node>& vars = d_qreg.d_vars[q];
  Assert(tsize == vars.size());
  std::map<TNode, TNode> subs;
  for (size_t i = 0; i < tsize; i++)
  {
    subs[vars[i]] = terms[i];
  }
  // get the instantiation body
  InferenceId idNone = InferenceId::UNKNOWN;
  Node nulln;
  Node ibody = getInstantiation(q, vars, terms, idNone, nulln, doVts);
  ibody = rewrite(ibody);
  for (size_t i = 0; i < tsize; i++)
  {
    // process consecutively in reverse order, which is important since we use
    // the fail mask for incrementing in a lexicographic order
    size_t ii = (tsize - 1) - i;
    // replace with the identity substitution
    Node prev = terms[ii];
    terms[ii] = vars[ii];
    subs.erase(vars[ii]);
    if (subs.empty())
    {
      // will never succeed with empty substitution
      break;
    }
    Trace("inst-exp-fail") << "- revert " << ii << std::endl;
    // check whether we are still redundant
    bool success = false;
    // check entailment, only if option is set
    if (options().quantifiers.instNoEntail)
    {
      Trace("inst-exp-fail") << "  check entailment" << std::endl;
      success = echeck->isEntailed(q[1], subs, false, true);
      Trace("inst-exp-fail") << "  entailed: " << success << std::endl;
    }
    // check whether the instantiation rewrites to the same thing
    if (!success)
    {
      Node ibodyc = getInstantiation(q, vars, terms, idNone, nulln, doVts);
      ibodyc = rewrite(ibodyc);
      success = (ibodyc == ibody);
      Trace("inst-exp-fail") << "  rewrite invariant: " << success << std::endl;
    }
    if (success)
    {
      // if we still fail, we are not critical
      failMask[ii] = false;
    }
    else
    {
      subs[vars[ii]] = prev;
      terms[ii] = prev;
      // not necessary to proceed if expFull is false
      if (!expFull)
      {
        break;
      }
    }
  }
  if (TraceIsOn("inst-exp-fail"))
  {
    Trace("inst-exp-fail") << "Fail mask: ";
    for (bool b : failMask)
    {
      Trace("inst-exp-fail") << (b ? 1 : 0);
    }
    Trace("inst-exp-fail") << std::endl;
  }
  return false;
}

void Instantiate::recordInstantiation(Node q,
                                      const std::vector<Node>& terms,
                                      bool doVts)
{
  Trace("inst-debug") << "Record instantiation for " << q << std::endl;
  // get the instantiation list, which ensures that q is marked as a quantified
  // formula we instantiated, despite only recording an instantiation here
  getOrMkInstLemmaList(q);
  Node inst = getInstantiation(q, terms, doVts);
  d_recordedInst[q].push_back(inst);
}

bool Instantiate::existsInstantiation(Node q, const std::vector<Node>& terms)
{
  if (options().base.incrementalSolving)
  {
    std::map<Node, CDInstMatchTrie*>::iterator it = d_c_inst_match_trie.find(q);
    if (it != d_c_inst_match_trie.end())
    {
      return it->second->existsInstMatch(userContext(), q, terms);
    }
  }
  else
  {
    std::map<Node, InstMatchTrie>::iterator it = d_inst_match_trie.find(q);
    if (it != d_inst_match_trie.end())
    {
      return it->second.existsInstMatch(q, terms);
    }
  }
  return false;
}

Node Instantiate::getInstantiation(Node q,
                                   const std::vector<Node>& vars,
                                   const std::vector<Node>& terms,
                                   InferenceId id,
                                   Node pfArg,
                                   bool doVts,
                                   LazyCDProof* pf)
{
  Assert(vars.size() == terms.size());
  Assert(q[0].getNumChildren() == vars.size());
  // Notice that this could be optimized, but no significant performance
  // improvements were observed with alternative implementations (see #1386).
  Node body =
      q[1].substitute(vars.begin(), vars.end(), terms.begin(), terms.end());

  // store the proof of the instantiated body, with (open) assumption q
  if (pf != nullptr)
  {
    // additional arguments: if the inference id is not unknown, include it,
    // followed by the proof argument if non-null. The latter is used e.g.
    // to track which trigger caused an instantiation.
    std::vector<Node> pfTerms = terms;
    if (id != InferenceId::UNKNOWN)
    {
      pfTerms.push_back(mkInferenceIdNode(id));
      if (!pfArg.isNull())
      {
        pfTerms.push_back(pfArg);
      }
    }
    pf->addStep(body, PfRule::INSTANTIATE, {q}, pfTerms);
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
                        PfRule::THEORY_PREPROCESS,
                        true,
                        "Instantiate::getInstantiation:rewrite_inst");
        pf->addStep(newBody, PfRule::EQ_RESOLVE, {body, proven}, {});
      }
      body = newBody;
    }
  }
  return body;
}

Node Instantiate::getInstantiation(Node q,
                                   const std::vector<Node>& terms,
                                   bool doVts)
{
  Assert(d_qreg.d_vars.find(q) != d_qreg.d_vars.end());
  return getInstantiation(
      q, d_qreg.d_vars[q], terms, InferenceId::UNKNOWN, Node::null(), doVts);
}

bool Instantiate::recordInstantiationInternal(Node q,
                                              const std::vector<Node>& terms)
{
  if (options().base.incrementalSolving)
  {
    Trace("inst-add-debug")
        << "Adding into context-dependent inst trie" << std::endl;
    const auto res = d_c_inst_match_trie.insert({q, nullptr});
    if (res.second)
    {
      res.first->second = new CDInstMatchTrie(userContext());
    }
    d_c_inst_match_trie_dom.insert(q);
    return res.first->second->addInstMatch(userContext(), q, terms);
  }
  Trace("inst-add-debug") << "Adding into inst trie" << std::endl;
  return d_inst_match_trie[q].addInstMatch(q, terms);
}

void Instantiate::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs) const
{
  for (NodeInstListMap::const_iterator it = d_insts.begin();
       it != d_insts.end();
       ++it)
  {
    qs.push_back(it->first);
  }
}

void Instantiate::getInstantiationTermVectors(
    Node q, std::vector<std::vector<Node> >& tvecs)
{
  if (options().base.incrementalSolving)
  {
    std::map<Node, CDInstMatchTrie*>::const_iterator it =
        d_c_inst_match_trie.find(q);
    if (it != d_c_inst_match_trie.end())
    {
      it->second->getInstantiations(q, tvecs);
    }
  }
  else
  {
    std::map<Node, InstMatchTrie>::const_iterator it =
        d_inst_match_trie.find(q);
    if (it != d_inst_match_trie.end())
    {
      it->second.getInstantiations(q, tvecs);
    }
  }
}

void Instantiate::getInstantiationTermVectors(
    std::map<Node, std::vector<std::vector<Node> > >& insts)
{
  if (options().base.incrementalSolving)
  {
    for (const auto& t : d_c_inst_match_trie)
    {
      getInstantiationTermVectors(t.first, insts[t.first]);
    }
  }
  else
  {
    for (const auto& t : d_inst_match_trie)
    {
      getInstantiationTermVectors(t.first, insts[t.first]);
    }
  }
}

void Instantiate::getInstantiations(Node q, std::vector<Node>& insts)
{
  Trace("inst-debug") << "get instantiations for " << q << std::endl;
  InstLemmaList* ill = getOrMkInstLemmaList(q);
  insts.insert(insts.end(), ill->d_list.begin(), ill->d_list.end());
  // also include recorded instantations (for qe-partial)
  std::map<Node, std::vector<Node> >::const_iterator it =
      d_recordedInst.find(q);
  if (it != d_recordedInst.end())
  {
    insts.insert(insts.end(), it->second.begin(), it->second.end());
  }
}

bool Instantiate::isProofEnabled() const
{
  return d_env.isTheoryProofProducing();
}

void Instantiate::notifyEndRound()
{
  // debug information
  if (TraceIsOn("inst-per-quant-round"))
  {
    for (std::pair<const Node, uint32_t>& i : d_instDebugTemp)
    {
      Trace("inst-per-quant-round")
          << " * " << i.second << " for " << i.first << std::endl;
    }
  }
  if (isOutputOn(OutputTag::INST))
  {
    bool req = !options().quantifiers.printInstFull;
    for (std::pair<const Node, uint32_t>& i : d_instDebugTemp)
    {
      Node name;
      if (!d_qreg.getNameForQuant(i.first, name, req))
      {
        continue;
      }
      output(OutputTag::INST) << "(num-instantiations " << name << " "
                              << i.second << ")" << std::endl;
    }
  }
}

void Instantiate::debugPrintModel()
{
  if (TraceIsOn("inst-per-quant"))
  {
    for (NodeInstListMap::iterator it = d_insts.begin(); it != d_insts.end();
         ++it)
    {
      Trace("inst-per-quant") << " * " << (*it).second->d_list.size() << " for "
                              << (*it).first << std::endl;
    }
  }
}

Node Instantiate::ensureType(Node n, TypeNode tn)
{
  Trace("inst-add-debug2") << "Ensure " << n << " : " << tn << std::endl;
  TypeNode ntn = n.getType();
  if (ntn == tn)
  {
    return n;
  }
  if (tn.isInteger())
  {
    return NodeManager::currentNM()->mkNode(TO_INTEGER, n);
  }
  else if (tn.isReal())
  {
    return NodeManager::currentNM()->mkNode(TO_REAL, n);
  }
  return Node::null();
}

InstLemmaList* Instantiate::getOrMkInstLemmaList(TNode q)
{
  NodeInstListMap::iterator it = d_insts.find(q);
  if (it != d_insts.end())
  {
    return it->second.get();
  }
  std::shared_ptr<InstLemmaList> ill =
      std::make_shared<InstLemmaList>(userContext());
  d_insts.insert(q, ill);
  return ill.get();
}

Instantiate::Statistics::Statistics(StatisticsRegistry& sr)
    : d_instantiations(sr.registerInt("Instantiate::Instantiations_Total")),
      d_inst_duplicate(sr.registerInt("Instantiate::Duplicate_Inst")),
      d_inst_duplicate_eq(sr.registerInt("Instantiate::Duplicate_Inst_Eq")),
      d_inst_duplicate_ent(
          sr.registerInt("Instantiate::Duplicate_Inst_Entailed"))
{
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
