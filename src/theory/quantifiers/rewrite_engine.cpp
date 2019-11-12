/*********************                                                        */
/*! \file rewrite_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite engine module
 **
 ** This class manages rewrite rules for quantifiers
 **/

#include "theory/quantifiers/rewrite_engine.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

struct PrioritySort {
  std::vector< double > d_priority;
  bool operator() (int i,int j) {
    return d_priority[i] < d_priority[j];
  }
};

RewriteEngine::RewriteEngine(context::Context* c,
                             QuantifiersEngine* qe,
                             QuantConflictFind* qcf)
    : QuantifiersModule(qe), d_qcf(qcf)
{
  d_needsSort = false;
}

double RewriteEngine::getPriority( Node f ) {
  Node rr = QuantAttributes::getRewriteRule( f );
  Node rrr = rr[2];
  Trace("rr-priority") << "Get priority : " << rrr << " " << rrr.getKind() << std::endl;
  bool deterministic = rrr[1].getKind()!=OR;

  if( rrr.getKind()==RR_REWRITE ){
    return deterministic ? 0.0 : 3.0;
  }else if( rrr.getKind()==RR_DEDUCTION ){
    return deterministic ? 1.0 : 4.0;
  }else if( rrr.getKind()==RR_REDUCTION ){
    return deterministic ? 2.0 : 5.0;
  }else{
    return 6.0;
  }

  //return deterministic ? 0.0 : 1.0;
}

bool RewriteEngine::needsCheck( Theory::Effort e ){
  return e==Theory::EFFORT_FULL;
  //return e>=Theory::EFFORT_LAST_CALL;
}

void RewriteEngine::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    Assert(!d_quantEngine->inConflict());
    Trace("rewrite-engine") << "---Rewrite Engine Round, effort = " << e << "---" << std::endl;
    //if( e==Theory::EFFORT_LAST_CALL ){
    //  if( !d_quantEngine->getModel()->isModelSet() ){
    //    d_quantEngine->getTheoryEngine()->getModelBuilder()->buildModel( d_quantEngine->getModel(), true );
    //  }
    //}
    if( d_needsSort ){
      d_priority_order.clear();
      PrioritySort ps;
      std::vector< int > indicies;
      for( int i=0; i<(int)d_rr_quant.size(); i++ ){
        ps.d_priority.push_back( getPriority( d_rr_quant[i] ) );
        indicies.push_back( i );
      }
      std::sort( indicies.begin(), indicies.end(), ps );
      for( unsigned i=0; i<indicies.size(); i++ ){
        d_priority_order.push_back( d_rr_quant[indicies[i]] );
      }
      d_needsSort = false;
    }

    //apply rewrite rules
    int addedLemmas = 0;
    //per priority level
    int index = 0;
    bool success = true;
    while( !d_quantEngine->inConflict() && success && index<(int)d_priority_order.size() ) {
      addedLemmas += checkRewriteRule( d_priority_order[index], e );
      index++;
      if( index<(int)d_priority_order.size() ){
        success = addedLemmas==0 || getPriority( d_priority_order[index] )==getPriority( d_priority_order[index-1] );
      }
    }

    Trace("rewrite-engine") << "Finished rewrite engine, added " << addedLemmas << " lemmas." << std::endl;
  }
}

int RewriteEngine::checkRewriteRule( Node f, Theory::Effort e ) {
  Trace("rewrite-engine-inst") << "Check " << d_qinfo_n[f] << ", priority = " << getPriority( f ) << ", effort = " << e << "..." << std::endl;

  // get the proper quantifiers info
  std::map<Node, QuantInfo>::iterator it = d_qinfo.find(f);
  if (it == d_qinfo.end())
  {
    Trace("rewrite-engine-inst-debug") << "...No qinfo." << std::endl;
    return 0;
  }
  // reset QCF module
  QuantInfo* qi = &it->second;
  if (!qi->matchGeneratorIsValid())
  {
    Trace("rewrite-engine-inst-debug") << "...Invalid qinfo." << std::endl;
    return 0;
  }
  d_qcf->setEffort(QuantConflictFind::EFFORT_CONFLICT);
  Node rr = QuantAttributes::getRewriteRule(f);
  Trace("rewrite-engine-inst-debug") << "   Reset round..." << std::endl;
  qi->reset_round(d_qcf);
  Trace("rewrite-engine-inst-debug") << "   Get matches..." << std::endl;
  int addedLemmas = 0;
  while (!d_quantEngine->inConflict() && qi->getNextMatch(d_qcf)
         && (addedLemmas == 0 || !options::rrOneInstPerRound()))
  {
    Trace("rewrite-engine-inst-debug")
        << "   Got match to complete..." << std::endl;
    qi->debugPrintMatch("rewrite-engine-inst-debug");
    std::vector<int> assigned;
    if (!qi->isMatchSpurious(d_qcf))
    {
      bool doContinue = false;
      bool success = true;
      int tempAddedLemmas = 0;
      while (!d_quantEngine->inConflict() && tempAddedLemmas == 0 && success
             && (addedLemmas == 0 || !options::rrOneInstPerRound()))
      {
        success = qi->completeMatch(d_qcf, assigned, doContinue);
        doContinue = true;
        if (success)
        {
          Trace("rewrite-engine-inst-debug")
              << "   Construct match..." << std::endl;
          std::vector<Node> inst;
          qi->getMatch(inst);
          if (Trace.isOn("rewrite-engine-inst-debug"))
          {
            Trace("rewrite-engine-inst-debug")
                << "   Add instantiation..." << std::endl;
            for (unsigned i = 0, nchild = f[0].getNumChildren(); i < nchild;
                 i++)
            {
              Trace("rewrite-engine-inst-debug") << "  " << f[0][i] << " -> ";
              if (i < inst.size())
              {
                Trace("rewrite-engine-inst-debug") << inst[i] << std::endl;
              }
              else
              {
                Trace("rewrite-engine-inst-debug")
                    << "OUT_OF_RANGE" << std::endl;
                Assert(false);
              }
            }
          }
          // resize to remove auxiliary variables
          if (inst.size() > f[0].getNumChildren())
          {
            inst.resize(f[0].getNumChildren());
          }
          if (d_quantEngine->getInstantiate()->addInstantiation(f, inst))
          {
            addedLemmas++;
            tempAddedLemmas++;
          }
          else
          {
            Trace("rewrite-engine-inst-debug") << "   - failed." << std::endl;
          }
          Trace("rewrite-engine-inst-debug")
              << "   Get next completion..." << std::endl;
        }
      }
      Trace("rewrite-engine-inst-debug")
          << "   - failed to complete." << std::endl;
    }
    else
    {
      Trace("rewrite-engine-inst-debug")
          << "   - match is spurious." << std::endl;
    }
    Trace("rewrite-engine-inst-debug") << "   Get next match..." << std::endl;
  }
  d_quantEngine->d_statistics.d_instantiations_rr += addedLemmas;
  Trace("rewrite-engine-inst") << "-> Generated " << addedLemmas << " lemmas." << std::endl;
  return addedLemmas;
}

void RewriteEngine::registerQuantifier( Node f ) {
  Node rr = QuantAttributes::getRewriteRule( f );
  if (rr.isNull())
  {
    return;
  }
  Trace("rr-register") << "Register quantifier " << f << std::endl;
  Trace("rr-register") << "  rewrite rule is : " << rr << std::endl;
  d_rr_quant.push_back(f);
  d_rr[f] = rr;
  d_needsSort = true;
  Trace("rr-register") << "  guard is : " << d_rr[f][1] << std::endl;

  std::vector<Node> qcfn_c;

  std::vector<Node> bvl;
  bvl.insert(bvl.end(), f[0].begin(), f[0].end());

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> cc;
  // add patterns
  for (unsigned i = 1, nchild = f[2].getNumChildren(); i < nchild; i++)
  {
    std::vector<Node> nc;
    for (const Node& pat : f[2][i])
    {
      Node nn;
      Node nbv = nm->mkBoundVar(pat.getType());
      if (pat.getType().isBoolean() && pat.getKind() != APPLY_UF)
      {
        nn = pat.negate();
      }
      else
      {
        nn = pat.eqNode(nbv).negate();
        bvl.push_back(nbv);
      }
      nc.push_back(nn);
    }
    if (!nc.empty())
    {
      Node n = nc.size() == 1 ? nc[0] : nm->mkNode(AND, nc);
      Trace("rr-register-debug") << "  pattern is " << n << std::endl;
      if (std::find(cc.begin(), cc.end(), n) == cc.end())
      {
        cc.push_back(n);
      }
    }
  }
  qcfn_c.push_back(nm->mkNode(BOUND_VAR_LIST, bvl));

  std::vector<Node> body_c;
  // add the guards
  if (d_rr[f][1].getKind() == AND)
  {
    for (const Node& g : d_rr[f][1])
    {
      if (MatchGen::isHandled(g))
      {
        body_c.push_back(g.negate());
      }
    }
  }
  else if (d_rr[f][1] != d_quantEngine->getTermUtil()->d_true)
  {
    if (MatchGen::isHandled(d_rr[f][1]))
    {
      body_c.push_back(d_rr[f][1].negate());
    }
  }
  // add the patterns to the body
  body_c.push_back(cc.size() == 1 ? cc[0] : nm->mkNode(AND, cc));
  // make the body
  qcfn_c.push_back(body_c.size() == 1 ? body_c[0] : nm->mkNode(OR, body_c));
  // make the quantified formula
  d_qinfo_n[f] = nm->mkNode(FORALL, qcfn_c);
  Trace("rr-register") << "  qcf formula is : " << d_qinfo_n[f] << std::endl;
  d_qinfo[f].initialize(d_qcf, d_qinfo_n[f], d_qinfo_n[f][1]);
}

void RewriteEngine::assertNode( Node n ) {

}

bool RewriteEngine::checkCompleteFor( Node q ) { 
  // by semantics of rewrite rules, saturation -> SAT 
  return std::find( d_rr_quant.begin(), d_rr_quant.end(), q )!=d_rr_quant.end();
}

Node RewriteEngine::getInstConstNode( Node n, Node q ) {
  std::map< Node, Node >::iterator it = d_inst_const_node[q].find( n );
  if( it==d_inst_const_node[q].end() ){
    Node nn =
        d_quantEngine->getTermUtil()->substituteBoundVariablesToInstConstants(
            n, q);
    d_inst_const_node[q][n] = nn;
    return nn;
  }else{
    return it->second;
  }
}
