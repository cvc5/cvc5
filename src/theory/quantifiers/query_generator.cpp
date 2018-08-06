/*********************                                                        */
/*! \file query_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of query_generator
 **/

#include "theory/quantifiers/query_generator.h"

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

QueryGenerator::QueryGenerator() : d_sampler(nullptr) {}

void QueryGenerator::initialize(SygusSampler* ss, unsigned deqThresh)
{
  d_sampler = ss;
  d_deq_thresh = deqThresh;
  d_svars.clear();
  d_sampler->getVariables(d_svars);
}

void QueryGenerator::addTerm(Node n, std::ostream& out)
{
  Trace("sygus-qgen") << "QueryGenerator::addTerm : " << n << std::endl;
  unsigned npts = d_sampler->getNumSamplePoints();
  TypeNode tn = n.getType();
  // TODO : as an optimization, use a shared lazy trie?

  // the queries we generate on this round
  std::vector<Node> queries;
  // the number of points each query in the above vector is true
  std::vector<unsigned> queriesPtTrue;
  // the sample point indices for which the above queries are true
  std::unordered_set<unsigned> indices;

  // predicate queries (if n is Boolean)
  if (tn.isBoolean())
  {
    std::map<Node, std::vector<unsigned> > ev_to_pt;
    unsigned index = 0;
    unsigned threshCount = 0;
    while (index < npts && threshCount < 2)
    {
      Node v = d_sampler->evaluate(n, index);
      ev_to_pt[v].push_back(index);
      if (ev_to_pt[v].size() == d_deq_thresh + 1)
      {
        threshCount++;
      }
      index++;
    }
    if (threshCount < 2)
    {
      for (const std::pair<Node, std::vector<unsigned> >& etp : ev_to_pt)
      {
        if (etp.second.size() < d_deq_thresh)
        {
          for (const unsigned& i : etp.second)
          {
            indices.insert(i);
          }
          Node qy = n;
          Assert(etp.first.isConst());
          if (!etp.first.getConst<bool>())
          {
            qy = qy.negate();
          }
          queries.push_back(qy);
          queriesPtTrue.push_back(etp.second.size());
        }
      }
    }
  }

  // equality queries
  findQueries(&d_qgt_trie[tn],
              n,
              queries,
              queriesPtTrue,
              indices);
  Assert(queries.size() == queriesPtTrue.size());
  if (queries.empty())
  {
    return;
  }
  Trace("sygus-qgen-debug")
      << "query: Check " << queries.size() << " queries..." << std::endl;
  LogicInfo linfo = smt::currentSmtEngine()->getLogicInfo();
  for (unsigned i = 0, nqueries = queries.size(); i < nqueries; i++)
  {
    Node qy = queries[i];
    // we have an interesting query
    out << "(query " << qy << ")  ; " << queriesPtTrue[i] << "/" << npts
        << std::endl;
    checkQuery(qy);
  }
  // for each new index, we may have a new conjunctive query
  NodeManager* nm = NodeManager::currentNM();
  for (const unsigned& i : indices)
  {
    std::vector<Node>& qsi = d_pt_to_queries[i];
    if (qsi.size() > 1)
    {
      // take two random queries
      std::random_shuffle(qsi.begin(), qsi.end());
      Node qy = nm->mkNode(AND, qsi[0], qsi[1]);
      checkQuery(qy);
    }
  }
  Trace("sygus-qgen-check") << "...finished." << std::endl;
}

void QueryGenerator::checkQuery(Node qy)
{
  Trace("sygus-qgen-check") << "  query: check " << qy << "..." << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  // make the satisfiability query
  bool needExport = false;
  ExprManagerMapCollection varMap;
  ExprManager em(nm->getOptions());
  std::unique_ptr<SmtEngine> queryChecker;
  initializeChecker(queryChecker, em, varMap, qy, needExport);
  Result r = queryChecker->checkSat();
  Trace("sygus-qgen-check") << "  query: ...got : " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    std::stringstream ss;
    ss << "--sygus-rr-query-gen detected unsoundness in CVC4 on input " << qy
       << "!";
    AlwaysAssert(false, ss.str().c_str());
  }
}

// FIXME: make robust up to irrelevant variables
void QueryGenerator::findQueries(LazyTrie* lt,
                                 Node n,
                                 std::vector<Node>& queries,
                                 std::vector<unsigned>& queriesPtTrue,
                                 std::unordered_set<unsigned>& indices)
{
  TypeNode tn = n.getType();
  std::vector<unsigned> deqIndex;
  std::vector<unsigned> eqIndex;
  
  
  LazyTrieEvaluator* ev = d_sampler;
  unsigned ntotal = d_sampler->getNumSamplePoints();
  unsigned index = 0;
  bool exact = true;
  bool pushEq = false;
  bool pushDeq = false;
  bool pre = true;
  std::vector< LazyTrie * > visitTr;
  std::vector< unsigned > currIndex;
  std::vector< bool > currExact;
  std::vector< bool > pushEqIndex;
  std::vector< bool > pushDeqIndex;
  std::vector< bool > preVisit;
  visitTr.push_back(lt);
  currIndex.push_back(0);
  currExact.push_back(true);
  pushEqIndex.push_back(false);
  pushDeqIndex.push_back(false);
  preVisit.push_back(true);
  do
  {
    lt = visitTr.back();
    index = currIndex.back();
    exact = currExact.back();
    pushEq = pushEqIndex.back();
    pushDeq = pushDeqIndex.back();
    pre = preVisit.back();
    if( !pre )
    {
      if( pushEq )
      {
        eqIndex.pop_back();
      }
      if( pushDeq )
      {
        deqIndex.pop_back();
      }    
      visitTr.pop_back();
      currIndex.pop_back();
      currExact.pop_back();
      pushEqIndex.pop_back();
      pushDeqIndex.pop_back();
      preVisit.pop_back();
    }
    else
    {
      preVisit[preVisit.size()-1] = false;
      if( pushEq )
      {
        eqIndex.push_back(index-1);
      }
      if( pushDeq )
      {
        deqIndex.push_back(index-1);
      }
      int deqAllow = d_deq_thresh - deqIndex.size();
      int eqAllow = d_deq_thresh - eqIndex.size();
      Trace("sygus-qgen-debug") << "Find queries " << n << " " << index << "/"
                                << ntotal << ", deq/eq allow = " << deqAllow << "/"
                                << eqAllow << ", exact = " << exact << std::endl;
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
          // if made it here,
          Assert(deqAllow >= 0 || eqAllow >= 0);
          Node query = n.eqNode(nAlmostEq);
          std::vector<unsigned> tIndices;
          if (eqAllow >= 0)
          {
            tIndices.insert(tIndices.end(), eqIndex.begin(), eqIndex.end());
          }
          else if (deqAllow >= 0)
          {
            query = query.negate();
            tIndices.insert(tIndices.end(), deqIndex.begin(), deqIndex.end());
          }
          AlwaysAssert(tIndices.size() <= d_deq_thresh);
          if (!tIndices.empty())
          {
            queries.push_back(query);
            queriesPtTrue.push_back(tIndices.size());
            for (unsigned& i : tIndices)
            {
              d_pt_to_queries[i].push_back(query);
              indices.insert(i);
            }
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
                currIndex.push_back(index+1);
                currExact.push_back(false);
                pushEqIndex.push_back(false);
                pushDeqIndex.push_back(true);
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
            currIndex.push_back(index+1);
            currExact.push_back(true);
            pushEqIndex.push_back(pushEqNext);
            pushDeqIndex.push_back(false);
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
            currIndex.push_back(index+1);
            currExact.push_back(false);
            pushEqIndex.push_back(pushEqNext);
            pushDeqIndex.push_back(false);
            preVisit.push_back(true);
          }
        }
      }
    }
  }while( !visitTr.empty() );
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
