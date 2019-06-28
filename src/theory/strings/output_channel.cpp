/*********************                                                        */
/*! \file output_channel.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/

#include "theory/strings/output_channel.h"

#include "expr/kind.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

OutputChannelStrings::OutputChannelStrings(context::Context* c, context::UserContext* u,eq::EqualityEngine& ee,
                      OutputChannel& out) : d_ee(ee), d_out(out),
      d_conflict(c, false),
      d_infer(c),
      d_infer_exp(c)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

bool OutputChannelStrings::sendInternalInference(std::vector<Node>& exp,
                                          Node conc,
                                          const char* c)
{
  if (conc.getKind() == AND
      || (conc.getKind() == NOT && conc[0].getKind() == OR))
  {
    Node conj = conc.getKind() == AND ? conc : conc[0];
    bool pol = conc.getKind() == AND;
    bool ret = true;
    for (const Node& cc : conj)
    {
      bool retc = sendInternalInference(exp, pol ? cc : cc.negate(), c);
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
      if (!lit[i].isConst() && !hasTerm(lit[i]))
      {
        // introduces a new non-constant term, do not infer
        return false;
      }
    }
    // does it already hold?
    if (pol ? areEqual(lit[0], lit[1]) : areDisequal(lit[0], lit[1]))
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
  else if (!hasTerm(lit))
  {
    // introduces a new non-constant term, do not infer
    return false;
  }
  else if (areEqual(lit, pol ? d_true : d_false))
  {
    // already holds
    return true;
  }
  sendInference(exp, conc, c);
  return true;
}

void OutputChannelStrings::sendInference( std::vector< Node >& exp, std::vector< Node >& exp_n, Node eq, const char * c, bool asLemma ) {
  eq = eq.isNull() ? d_false : Rewriter::rewrite( eq );
  if( eq!=d_true ){
    if( Trace.isOn("strings-infer-debug") ){
      Trace("strings-infer-debug") << "By " << c << ", infer : " << eq << " from: " << std::endl;
      for( unsigned i=0; i<exp.size(); i++ ){
        Trace("strings-infer-debug")  << "  " << exp[i] << std::endl;
      }
      for( unsigned i=0; i<exp_n.size(); i++ ){
        Trace("strings-infer-debug")  << "  N:" << exp_n[i] << std::endl;
      }
      //Trace("strings-infer-debug") << "as lemma : " << asLemma << std::endl;
    }
    //check if we should send a lemma or an inference
    if( asLemma || eq==d_false || eq.getKind()==OR || !exp_n.empty() || options::stringInferAsLemmas() ){  
      Node eq_exp;
      // FIXME
      /*
      if( options::stringRExplainLemmas() ){
        eq_exp = mkExplain( exp, exp_n );
      }else{
        if( exp.empty() ){
          eq_exp = mkAnd( exp_n );
        }else if( exp_n.empty() ){
          eq_exp = mkAnd( exp );
        }else{
          std::vector< Node > ev;
          ev.insert( ev.end(), exp.begin(), exp.end() );
          ev.insert( ev.end(), exp_n.begin(), exp_n.end() );
          eq_exp = NodeManager::currentNM()->mkNode( AND, ev );
        }
      }
      */
      // if we have unexplained literals, this lemma is not a conflict
      if (eq == d_false && !exp_n.empty())
      {
        eq = eq_exp.negate();
        eq_exp = d_true;
      }
      sendLemma( eq_exp, eq, c );
    }else{
      sendInfer( mkAnd( exp ), eq, c );
    }
  }
}

void OutputChannelStrings::sendInference( std::vector< Node >& exp, Node eq, const char * c, bool asLemma ) {
  std::vector< Node > exp_n;
  sendInference( exp, exp_n, eq, c, asLemma );
}

void OutputChannelStrings::sendLemma( Node ant, Node conc, const char * c ) {
  if( conc.isNull() || conc == d_false ) {
    Trace("strings-conflict") << "Strings::Conflict : " << c << " : " << ant << std::endl;
    Trace("strings-lemma") << "Strings::Conflict : " << c << " : " << ant << std::endl;
    Trace("strings-assert") << "(assert (not " << ant << ")) ; conflict " << c << std::endl;
    d_out.conflict(ant);
    d_conflict = true;
  } else {
    Node lem;
    if( ant == d_true ) {
      lem = conc;
    }else{
      lem = NodeManager::currentNM()->mkNode( IMPLIES, ant, conc );
    }
    Trace("strings-lemma") << "Strings::Lemma " << c << " : " << lem << std::endl;
    Trace("strings-assert") << "(assert " << lem << ") ; lemma " << c << std::endl;
    d_lemma_cache.push_back( lem );
  }
}

void OutputChannelStrings::sendInfer( Node eq_exp, Node eq, const char * c ) {
  if( options::stringInferSym() ){
    std::vector< Node > vars;
    std::vector< Node > subs;
    std::vector< Node > unproc;
    //FIXME
    //inferSubstitutionProxyVars( eq_exp, vars, subs, unproc );
    if( unproc.empty() ){
      Trace("strings-lemma-debug") << "Strings::Infer " << eq << " from " << eq_exp << " by " << c << std::endl;
      Node eqs = eq.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      Trace("strings-lemma-debug") << "Strings::Infer Alternate : " << eqs << std::endl;
      for( unsigned i=0; i<vars.size(); i++ ){
        Trace("strings-lemma-debug") << "  " << vars[i] << " -> " << subs[i] << std::endl;
      }
      sendLemma( d_true, eqs, c );
      return;
    }else{
      for( unsigned i=0; i<unproc.size(); i++ ){
        Trace("strings-lemma-debug") << "  non-trivial exp : " << unproc[i] << std::endl;
      }
    }
  }
  Trace("strings-lemma") << "Strings::Infer " << eq << " from " << eq_exp << " by " << c << std::endl;
  Trace("strings-assert") << "(assert (=> " << eq_exp << " " << eq << ")) ; infer " << c << std::endl;
  d_pending.push_back( eq );
  d_pending_exp[eq] = eq_exp;
  d_infer.push_back( eq );
  d_infer_exp.push_back( eq_exp );
}

bool OutputChannelStrings::sendSplit(Node a, Node b, const char* c, bool preq)
{
  Node eq = a.eqNode( b );
  eq = Rewriter::rewrite( eq );
  if (eq.isConst())
  {
    return false;
  }
  Node neq = NodeManager::currentNM()->mkNode(NOT, eq);
  Node lemma_or = NodeManager::currentNM()->mkNode(OR, eq, neq);
  Trace("strings-lemma") << "Strings::Lemma " << c << " SPLIT : " << lemma_or
                          << std::endl;
  d_lemma_cache.push_back(lemma_or);
  d_pending_req_phase[eq] = preq;
  return true;
}


Node OutputChannelStrings::getRepresentative( Node t ) {
  if( d_ee.hasTerm( t ) ){
    return d_ee.getRepresentative( t );
  }
  return t;
}

bool OutputChannelStrings::hasTerm( Node a ){
  return d_ee.hasTerm( a );
}

bool OutputChannelStrings::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_ee.areEqual( a, b );
  }
  return false;
}

bool OutputChannelStrings::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }
  if( hasTerm( a ) && hasTerm( b ) ) {
    Node ar = d_ee.getRepresentative( a );
    Node br = d_ee.getRepresentative( b );
    return ( ar!=br && ar.isConst() && br.isConst() ) || d_ee.areDisequal( ar, br, false );
  }
  Node ar = getRepresentative( a );
  Node br = getRepresentative( b );
  return ar!=br && ar.isConst() && br.isConst();
}

Node OutputChannelStrings::mkAnd( std::vector< Node >& a ) {
  std::vector< Node > au;
  for( const Node& ai : a ){
    if( std::find( au.begin(), au.end(), ai )==au.end() ){
      au.push_back( ai );
    }
  }
  if( au.empty() ) {
    return NodeManager::currentNM()->mkConst(true);
  } else if( au.size() == 1 ) {
    return au[0];
  }
  return NodeManager::currentNM()->mkNode( AND, au );
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
