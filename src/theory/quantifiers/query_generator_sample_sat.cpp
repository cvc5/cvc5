/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a class for mining interesting satisfiability
 * queries from a stream of generated expressions.
 */

#include "theory/quantifiers/query_generator_sample_sat.h"

#include <fstream>
#include <sstream>

#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "smt/print_benchmark.h"
#include "util/random.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QueryGeneratorSampleSat::QueryGeneratorSampleSat(Env& env, unsigned deqThresh)
    : QueryGenerator(env), d_deqThresh(deqThresh)
{
}

bool QueryGeneratorSampleSat::addTerm(Node n, std::vector<Node>& foundQueries)
{
  Node nn = n.getKind() == NOT ? n[0] : n;
  if (d_terms.find(nn) != d_terms.end())
  {
    return false;
  }
  d_terms.insert(nn);

  Trace("sygus-qgen") << "QueryGeneratorSampleSat::addTerm : " << n
                      << std::endl;
  unsigned npts = d_sampler->getNumSamplePoints();
  TypeNode tn = n.getType();
  // TODO : as an optimization, use a shared lazy trie?

  // the queries we generate on this round
  std::vector<Node> queries;
  // For each query in the above vector, this stores the indices of the points
  // for which that query evaluated to true on.
  std::vector<std::vector<unsigned>> queriesPtTrue;
  // the sample point indices for which the above queries are true
  std::unordered_set<unsigned> indices;

  // collect predicate queries (if n is Boolean)
  if (tn.isBoolean())
  {
    std::map<Node, std::vector<unsigned>> ev_to_pt;
    unsigned index = 0;
    // the number of {true,false} for which the #points evaluated to that
    // constant is greater than the threshold.
    unsigned threshCount = 0;
    while (index < npts && threshCount < 2)
    {
      Node v = d_sampler->evaluate(nn, index);
      // it may not evaluate, in which case we ignore the point
      if (v.isConst())
      {
        ev_to_pt[v].push_back(index);
        if (ev_to_pt[v].size() == d_deqThresh + 1)
        {
          threshCount++;
        }
      }
      index++;
    }
    if (threshCount < 2)
    {
      for (const auto& etp : ev_to_pt)
      {
        if (etp.second.size() < d_deqThresh)
        {
          indices.insert(etp.second.begin(), etp.second.end());
          Node qy = nn;
          Assert(etp.first.isConst());
          if (!etp.first.getConst<bool>())
          {
            qy = qy.negate();
          }
          queries.push_back(qy);
          queriesPtTrue.push_back(etp.second);
        }
      }
    }
  }

  // collect equality queries
  findQueries(nn, queries, queriesPtTrue);
  Assert(queries.size() == queriesPtTrue.size());
  if (queries.empty())
  {
    return true;
  }
  Trace("sygus-qgen-debug")
      << "query: Check " << queries.size() << " queries..." << std::endl;
  // literal queries
  for (unsigned i = 0, nqueries = queries.size(); i < nqueries; i++)
  {
    Node qy = queries[i];
    std::vector<unsigned>& tIndices = queriesPtTrue[i];
    // we have an interesting query
    Trace("sygus-qgen-debug")
        << "; " << tIndices.size() << "/" << npts << std::endl;
    AlwaysAssert(!tIndices.empty());
    checkQuery(qy, tIndices[0], foundQueries);
    // add information
    for (unsigned& ti : tIndices)
    {
      d_ptToQueries[ti].push_back(qy);
      d_qysToPoints[qy].push_back(ti);
      indices.insert(ti);
    }
  }
  // for each new index, we may have a new conjunctive query
  NodeManager* nm = NodeManager::currentNM();
  for (const unsigned& i : indices)
  {
    std::vector<Node>& qsi = d_ptToQueries[i];
    if (qsi.size() > 1)
    {
      // take two random queries
      size_t rindex = Random::getRandom().pick(0, qsi.size() - 1);
      size_t rindex2 = Random::getRandom().pick(0, qsi.size() - 2);
      if (rindex2 >= rindex)
      {
        rindex2 = rindex2 + 1;
      }
      Node qy = nm->mkNode(AND, qsi[rindex], qsi[rindex2]);
      checkQuery(qy, i, foundQueries);
    }
  }
  Trace("expr-miner-check") << "...finished." << std::endl;
  return true;
}

void QueryGeneratorSampleSat::checkQuery(Node qy,
                                         unsigned spIndex,
                                         std::vector<Node>& foundQueries)
{
  if (d_allQueries.find(qy) != d_allQueries.end())
  {
    return;
  }
  d_allQueries.insert(qy);
  // external query

  Result r;
  Trace("expr-miner-check") << "Check (qgss): " << qy << "..." << std::endl;
  // make the satisfiability query
  SubsolverSetupInfo ssi(d_env);
  std::unique_ptr<SolverEngine> queryChecker;
  initializeChecker(queryChecker, qy, ssi);
  r = queryChecker->checkSat();
  Trace("expr-miner-check") << "...result: " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    std::stringstream ss;
    ss << "--sygus-rr-query-gen detected unsoundness in cvc5 on input " << qy
       << "!" << std::endl;
    ss << "This query has a model : " << std::endl;
    const std::vector<Node>& pt = d_sampler->getSamplePoint(spIndex);
    Assert(pt.size() == d_vars.size());
    for (unsigned i = 0, size = pt.size(); i < size; i++)
    {
      ss << "  " << d_vars[i] << " -> " << pt[i] << std::endl;
    }
    ss << "but cvc5 answered unsat!" << std::endl;
    AlwaysAssert(false) << ss.str();
  }
  dumpQuery(qy, r, foundQueries);
}

void QueryGeneratorSampleSat::findQueries(
    Node n,
    std::vector<Node>& queries,
    std::vector<std::vector<unsigned>>& queriesPtTrue)
{
  // At a high level, this method traverses the LazyTrie for the type of n
  // and tries to find paths to leafs that contain terms n' such that n = n'
  // or n != n' is an interesting query, i.e. satisfied for a small number of
  // points.
  TypeNode tn = n.getType();
  LazyTrie* lt = &d_qgtTrie[tn];
  // These vectors are the set of indices of sample points for which the current
  // node we are considering are { equal, disequal } from n.
  std::vector<unsigned> eqIndex[2];
  Trace("sygus-qgen-debug") << "Compute queries for " << n << "...\n";

  LazyTrieEvaluator* ev = d_sampler;
  unsigned ntotal = d_sampler->getNumSamplePoints();
  unsigned index = 0;
  bool exact = true;
  bool pushEq[2] = {false, false};
  bool pre = true;
  // The following parallel vectors describe the state of the locations in the
  // trie we are currently visiting.
  // Reference to the location in the trie
  std::vector<LazyTrie*> visitTr;
  // The index of the sample point we are testing
  std::vector<unsigned> currIndex;
  // Whether the path to this location exactly matches the evaluation of n
  std::vector<bool> currExact;
  // Whether we are adding to the points that are { equal, disequal } by
  // traversing to this location.
  std::vector<bool> pushIndex[2];
  // Whether we are in a pre-traversal for this location.
  std::vector<bool> preVisit;
  visitTr.push_back(lt);
  currIndex.push_back(0);
  currExact.push_back(true);
  pushIndex[0].push_back(false);
  pushIndex[1].push_back(false);
  preVisit.push_back(true);
  do
  {
    lt = visitTr.back();
    index = currIndex.back();
    exact = currExact.back();
    for (unsigned r = 0; r < 2; r++)
    {
      pushEq[r] = pushIndex[r].back();
    }
    pre = preVisit.back();
    if (!pre)
    {
      visitTr.pop_back();
      currIndex.pop_back();
      currExact.pop_back();
      preVisit.pop_back();
      // clean up the indices of points that are { equal, disequal }
      for (unsigned r = 0; r < 2; r++)
      {
        if (pushEq[r])
        {
          eqIndex[r].pop_back();
        }
        pushIndex[r].pop_back();
      }
    }
    else
    {
      preVisit[preVisit.size() - 1] = false;
      // add to the indices of points that are { equal, disequal }
      for (unsigned r = 0; r < 2; r++)
      {
        if (pushEq[r])
        {
          eqIndex[r].push_back(index - 1);
        }
      }
      int eqAllow = d_deqThresh - eqIndex[0].size();
      int deqAllow = d_deqThresh - eqIndex[1].size();
      Trace("sygus-qgen-debug")
          << "Find queries " << n << " " << index << "/" << ntotal
          << ", deq/eq allow = " << deqAllow << "/" << eqAllow
          << ", exact = " << exact << std::endl;
      if (index == ntotal)
      {
        if (exact)
        {
          // add to the trie
          lt->d_lazy_child = n;
        }
        else
        {
          Node nAlmostEq = lt->d_lazy_child;
          // if made it here, we still should have either a equality or
          // a disequality that is allowed.
          Assert(deqAllow >= 0 || eqAllow >= 0);
          Node query = n.eqNode(nAlmostEq);
          std::vector<unsigned> tIndices;
          if (eqAllow >= 0)
          {
            tIndices.insert(
                tIndices.end(), eqIndex[0].begin(), eqIndex[0].end());
          }
          else if (deqAllow >= 0)
          {
            query = query.negate();
            tIndices.insert(
                tIndices.end(), eqIndex[1].begin(), eqIndex[1].end());
          }
          AlwaysAssert(tIndices.size() <= d_deqThresh);
          if (!tIndices.empty())
          {
            queries.push_back(query);
            queriesPtTrue.push_back(tIndices);
          }
        }
      }
      else
      {
        if (!lt->d_lazy_child.isNull())
        {
          // if there is a lazy child here, push
          Node e_lc = ev->evaluate(lt->d_lazy_child, index);
          // store at next level
          lt->d_children[e_lc].d_lazy_child = lt->d_lazy_child;
          // replace
          lt->d_lazy_child = Node::null();
        }
        // compute
        Node e_this = ev->evaluate(n, index);

        if (deqAllow >= 0)
        {
          // recursing on disequal points
          deqAllow--;
          // if there is use continuing
          if (deqAllow >= 0 || eqAllow >= 0)
          {
            for (std::pair<const Node, LazyTrie>& ltc : lt->d_children)
            {
              if (ltc.first != e_this)
              {
                visitTr.push_back(&ltc.second);
                currIndex.push_back(index + 1);
                currExact.push_back(false);
                pushIndex[0].push_back(false);
                pushIndex[1].push_back(true);
                preVisit.push_back(true);
              }
            }
          }
          deqAllow++;
        }
        bool pushEqNext = false;
        if (eqAllow >= 0)
        {
          // below, we try recursing (if at all) on equal nodes.
          eqAllow--;
          pushEqNext = true;
        }
        // if we are on the exact path of n
        if (exact)
        {
          if (lt->d_children.empty())
          {
            // if no one has been here before, we are done
            lt->d_lazy_child = n;
          }
          else
          {
            // otherwise, we recurse on the equal point
            visitTr.push_back(&(lt->d_children[e_this]));
            currIndex.push_back(index + 1);
            currExact.push_back(true);
            pushIndex[0].push_back(pushEqNext);
            pushIndex[1].push_back(false);
            preVisit.push_back(true);
          }
        }
        else if (deqAllow >= 0 || eqAllow >= 0)
        {
          // recurse on the equal point if it exists
          std::map<Node, LazyTrie>::iterator iteq = lt->d_children.find(e_this);
          if (iteq != lt->d_children.end())
          {
            visitTr.push_back(&(iteq->second));
            currIndex.push_back(index + 1);
            currExact.push_back(false);
            pushIndex[0].push_back(pushEqNext);
            pushIndex[1].push_back(false);
            preVisit.push_back(true);
          }
        }
      }
    }
  } while (!visitTr.empty());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
