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

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

QueryGenerator::QueryGenerator() : d_sampler(nullptr) {}

void QueryGenerator::initialize(SygusSampler* ss, unsigned deqThresh) { d_sampler = ss; d_deq_thresh = deqThresh; }

void QueryGenerator::addTerm(Node n,
                                       std::ostream& out)
{
  Trace("sygus-qg") << "QueryGenerator::addTerm : " << n << std::endl;
  unsigned npts = d_sampler->getNumSamplePoints();
  TypeNode tn = n.getType();
  // TODO : as an optimization, use a shared lazy trie?
  std::vector< Node > queries;
  std::vector<unsigned> queriesPtTrue;
  findQueries( &d_qgt_trie[tn], n, d_sampler, 0, npts, d_deq_thresh, d_deq_thresh, true, queries,queriesPtTrue );
  Assert( queries.size()==queriesPtTrue.size() );
  if( queries.empty() )
  {
    return;
  }
  Trace("sygus-qg-debug") << "query: Check " << queries.size() << " queries..." << std::endl;
  ExprManager * em = NodeManager::currentNM()->toExprManager();
  LogicInfo linfo = smt::currentSmtEngine()->getLogicInfo();
  for( unsigned i=0,nqueries=queries.size(); i<nqueries; i++ )
  {
    Node qy = queries[i];
    // we have an interesting query
    out << "(query " << qy << ")  ; " << queriesPtTrue[i] << "/" << npts << std::endl;
    Trace("sygus-qg-check") << "query: check " << qy << "..." << std::endl;
    Node qs = convertToSkolem(qy);
    
    // make the satisfiability query
    SmtEngine queryChecker(em);
    queryChecker.setLogic(linfo);
    queryChecker.assertFormula(qs.toExpr());
    Result r = queryChecker.checkSat();
    Trace("sygus-qg-check") << "query: ...got : " << r << std::endl;
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT )
    {
      std::stringstream ss;
      ss << "--sygus-rr-query-gen detected unsoundness in CVC4 on input " << qy << "!";
      AlwaysAssert(
          false,
          ss.str().c_str());
    }
  }
  Trace("sygus-qg-check") << "...finished." << std::endl;
}

void QueryGenerator::findQueries(
            LazyTrie * lt,
            Node n,
            LazyTrieEvaluator* ev,
            unsigned index,
            unsigned ntotal,
            int deqAllow,
            int eqAllow,
            bool exact,
            std::vector< Node >& queries,
               std::vector<unsigned>& queriesPtTrue
                                )
{
  Trace("sygus-qg-debug") << "Find queries " << n << " " << index << "/" << ntotal << ", deq/eq allow = " << deqAllow << "/" << eqAllow << ", exact = " << exact << std::endl;
  Assert( lt!=nullptr );
  Assert( ev!=nullptr );
  if( index==ntotal )
  {
    if( exact )
    {
      // add to the trie
      lt->d_lazy_child = n;
    }
    else
    {
      Node n_almost_eq = lt->d_lazy_child;
      // if made it here, 
      Assert( deqAllow>=0 || eqAllow>=0 );
      Node query = n.eqNode(n_almost_eq);
      unsigned numPtsQueryTrue = 0;
      if( eqAllow>=0 )
      {
        numPtsQueryTrue = d_deq_thresh-eqAllow;
      }
      else if( deqAllow>=0 )
      {
        query = query.negate();        
        numPtsQueryTrue = d_deq_thresh-deqAllow;
      }
      if( numPtsQueryTrue>0 )
      {
        queries.push_back(query);
        queriesPtTrue.push_back(numPtsQueryTrue);
      }
    }
    return;
  }
  
  if( !lt->d_lazy_child.isNull())
  {
    // if there is a lazy child here, push
    Node e_lc = ev->evaluate(lt->d_lazy_child, index);
    // store at next level
    lt->d_children[e_lc].d_lazy_child = lt->d_lazy_child;
    // replace
    lt->d_lazy_child = Node::null();
  }
  // compute
  Node e_this = ev->evaluate(n,index);
  
  if( deqAllow>=0 )
  {
    // recursing on disequal points
    deqAllow--;
    // if there is use continuing
    if( deqAllow>=0 || eqAllow>=0 )
    {
      for( std::pair<const Node, LazyTrie>& ltc : lt->d_children )
      {
        if( ltc.first!=e_this )
        {
          findQueries(&ltc.second,n,ev,index+1,ntotal,deqAllow,eqAllow,false, queries,queriesPtTrue);
        }
      }
    }
    deqAllow++;
  }
  if( eqAllow>=0 )
  {
    // below, we try recursing (if at all) on equal nodes.
    eqAllow--;
  }
  
  // if we are on the exact path of n
  if( exact )
  {
    if( lt->d_children.empty() )
    {
      // if no one has been here before, we are done
      lt->d_lazy_child = n;
    }
    else
    {
      // otherwise, we recurse on the equal point
      findQueries(&(lt->d_children[e_this]),n,ev,index+1,ntotal,deqAllow,eqAllow,true, queries,queriesPtTrue);
    }
    return;
  }
  
  // if it is worthwhile continuing
  if( deqAllow>=0 || eqAllow>=0 )
  {
    // recurse on the equal point if it exists
    std::map<Node, LazyTrie>::iterator iteq = lt->d_children.find(e_this);
    if( iteq!=lt->d_children.end() )
    {
      findQueries(&(iteq->second),n,ev,index+1,ntotal,deqAllow,eqAllow,false, queries,queriesPtTrue);
    }
  }
}
  
}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
