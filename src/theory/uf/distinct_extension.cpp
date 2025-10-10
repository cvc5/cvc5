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
 * The distinct extension of TheoryUF.
 */

#include "theory/uf/distinct_extension.h"

#include "options/smt_options.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "theory/uf/theory_uf_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

DistinctExtension::DistinctExtension(Env& env,
                                     TheoryState& state,
                                     TheoryInferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_ndistinct(context()),
      d_negDistinct(context()),
      d_negDistinctIndex(context(), 0),
      d_posDistinct(context()),
      d_dproof(nullptr),
      d_epg(d_env.isTheoryProofProducing()
                ? new EagerProofGenerator(d_env, context(), "DistinctEpg")
                : nullptr),
      d_pendingConflict(context())
{
  d_false = nodeManager()->mkConst(false);
}

bool DistinctExtension::needsCheckLastEffort()
{
  return d_negDistinctIndex.get() < d_negDistinct.size()
         || !d_posDistinct.empty();
}

void DistinctExtension::assertDistinct(TNode atom, bool pol, TNode fact)
{
  for (const Node& nc : atom)
  {
    d_state.addTerm(nc);
  }
  if (pol)
  {
    d_posDistinct.push_back(fact);
    std::unordered_map<Node, Node> reps;
    std::unordered_map<Node, Node>::iterator itr;
    bool isConflict = false;
    for (const Node& nc : atom)
    {
      Node ncr = d_state.getRepresentative(nc);
      itr = reps.find(ncr);
      if (itr == reps.end())
      {
        reps[ncr] = nc;
        continue;
      }
      isConflict = true;
      // otherwise already a conflict
      Node eq = itr->second.eqNode(nc);
      d_im.conflictExp(InferenceId::UF_DISTINCT_DEQ, {eq, fact}, d_epg.get());
      break;
    }
    if (!isConflict)
    {
      for (const std::pair<const Node, Node>& p : reps)
      {
        Trace("uf-lazy-distinct")
            << "Watch " << p.first << " distinct (" << fact << ")" << std::endl;
        size_t ndprev = d_ndistinct[p.first];
        d_ndistinct[p.first] = ndprev + 1;
        // ensure the non-context dependent list has the right size in
        // case we backtracked
        std::vector<Node>& ndlist = d_eqcToDistinct[p.first];
        ndlist.resize(ndprev);
        ndlist.emplace_back(fact);
        // also carry the member
        std::vector<Node>& ndmem = d_eqcToDMem[p.first];
        ndmem.resize(ndprev);
        ndmem.emplace_back(p.second);
      }
    }
  }
  else
  {
    // otherwise track that the negated distinct term
    d_negDistinct.push_back(fact);
  }
}

void DistinctExtension::eqNotifyMerge(TNode t1, TNode t2)
{
  // Must ensure we track distinct constraints, moving those from t2 into t1.
  // If the same distinct constraint is in both, we are in conflict.
  NodeUIntMap::iterator it2 = d_ndistinct.find(t2);
  if (it2 != d_ndistinct.end())
  {
    Trace("uf-lazy-distinct") << "merge " << t1 << " and " << t2 << std::endl;
    NodeUIntMap::iterator it1 = d_ndistinct.find(t1);
    std::vector<Node>& d1 = d_eqcToDistinct[t1];
    std::vector<Node>& d1m = d_eqcToDMem[t1];
    std::vector<Node>& d2 = d_eqcToDistinct[t2];
    // the iterator up to which d2 is valid
    std::vector<Node>::iterator d2e = d2.begin() + it2->second;
    if (it1 != d_ndistinct.end())
    {
      // ensure the list of distinct constraints in t1 is resized now
      d1.resize(it1->second);
      d1m.resize(it1->second);
      Trace("uf-lazy-distinct")
          << "...looking for conflicts in intersection of # terms = "
          << it1->second << " and " << it2->second << std::endl;
      // check for conflicts
      for (size_t i = 0; i < it1->second; i++)
      {
        Node d = d1[i];
        Assert(d.getKind() == Kind::DISTINCT);
        Trace("uf-lazy-distinct") << "...check " << d << std::endl;
        std::vector<Node>::iterator itd1 = std::find(d2.begin(), d2e, d);
        if (itd1 != d2e)
        {
          // conflict
          size_t i2 = std::distance(d2.begin(), itd1);
          Assert(i < d_eqcToDMem[t1].size());
          Assert(i2 < d_eqcToDMem[t2].size());
          Node eq = d_eqcToDMem[t1][i].eqNode(d_eqcToDMem[t2][i2]);
          Assert(d_state.areEqual(d_eqcToDMem[t1][i], d_eqcToDMem[t2][i2]));
          Trace("uf-lazy-distinct")
              << "...conflict " << eq << " " << d << std::endl;
          std::vector<Node> exp{eq, d};
          d_pendingConflict = nodeManager()->mkAnd(exp);
          return;
        }
        Trace("uf-lazy-distinct") << "...no conflict" << std::endl;
      }
    }
    else
    {
      d1.clear();
      d1m.clear();
    }
    // append lists
    d1.insert(d1.end(), d2.begin(), d2e);
    std::vector<Node>& d2m = d_eqcToDMem[t2];
    d1m.insert(d1m.end(), d2m.begin(), d2m.begin() + it2->second);
  }
}

void DistinctExtension::check(Theory::Effort level)
{
  if (!d_pendingConflict.get().isNull())
  {
    Node conf = d_pendingConflict.get();
    std::vector<Node> exp(conf.begin(), conf.end());
    d_im.conflictExp(InferenceId::UF_DISTINCT_DEQ, exp, d_epg.get());
    return;
  }
  if (level != Theory::Effort::EFFORT_LAST_CALL)
  {
    return;
  }
  TheoryModel* tm = d_state.getModel();
  bool addedLemma = false;
  // check negated distinct
  size_t nnd = d_negDistinct.size();
  for (size_t i = d_negDistinctIndex.get(); i < nnd; i++)
  {
    Node ndistinct = d_negDistinct[i];
    Assert(ndistinct.getKind() == Kind::NOT
           && ndistinct[0].getKind() == Kind::DISTINCT);
    // check if satisfied
    Node atom = ndistinct[0];
    std::unordered_set<Node> reps;
    bool isSat = false;
    for (size_t j = 0, nterms = atom.getNumChildren(); j < nterms; j++)
    {
      Node ncr = d_state.getRepresentative(atom[j]);
      if (!reps.insert(ncr).second)
      {
        isSat = true;
        break;
      }
    }
    if (!isSat)
    {
      Node batom = TheoryUfRewriter::blastDistinct(nodeManager(), atom);
      Node lem = nodeManager()->mkNode(Kind::IMPLIES, batom, atom);
      TrustNode tlem = TrustNode::mkTrustLemma(lem, nullptr);
      if (d_im.trustedLemma(tlem, InferenceId::UF_NOT_DISTINCT_ELIM))
      {
        addedLemma = true;
      }
    }
    // otherwise we determined that we are SAT in the remainder of this
    // SAT context (due to looking up representatives, instead of model values)
    // meaning that we don't need to check this constraint again in this
    // SAT context.
  }
  d_negDistinctIndex = nnd;
  if (addedLemma)
  {
    return;
  }
  // Note that it still may the case that we have a (distinct t1 ... tn)
  // constraint where ti and tj were assigned the same value in the model,
  // but the UF theory was not informed of ti = tj. This is because we
  // do not insist that distinct induces care pairs in theory combination.
  // Thus we must double check that are values are distinct in the model.
  // If not, then we add the lemma (~distinct(t1,...,tn) or ti != tj).
  for (const Node& atom : d_posDistinct)
  {
    Assert(atom.getKind() == Kind::DISTINCT);
    // ensure the positive distinct are satisfied in model
    std::unordered_map<Node, Node> vals;
    std::unordered_map<Node, Node>::iterator itr;
    for (const Node& nc : atom)
    {
      Node ncr = tm->getValue(nc);
      itr = vals.find(ncr);
      if (itr == vals.end())
      {
        vals[ncr] = nc;
        continue;
      }
      Node eq = itr->second.eqNode(nc);
      Node lem = nodeManager()->mkNode(Kind::AND, {eq, atom}).notNode();
      TrustNode tlem = TrustNode::mkTrustLemma(lem, nullptr);
      d_im.trustedLemma(tlem, InferenceId::UF_DISTINCT_DEQ_MODEL);
    }
  }
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
