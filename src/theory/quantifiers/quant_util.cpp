/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifier utilities
 */

#include "theory/quantifiers/quant_util.h"

#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

QuantifiersUtil::QuantifiersUtil(Env& env) : EnvObj(env) {}

QuantPhaseReq::QuantPhaseReq( Node n, bool computeEq ){
  initialize( n, computeEq );
}

void QuantPhaseReq::initialize( Node n, bool computeEq ){
  std::map< Node, int > phaseReqs2;
  computePhaseReqs( n, false, phaseReqs2 );
  for( std::map< Node, int >::iterator it = phaseReqs2.begin(); it != phaseReqs2.end(); ++it ){
    if( it->second==1 ){
      d_phase_reqs[ it->first ] = true;
    }else if( it->second==-1 ){
      d_phase_reqs[ it->first ] = false;
    }
  }
  Trace("inst-engine-phase-req") << "Phase requirements for " << n << ":" << std::endl;
  //now, compute if any patterns are equality required
  if( computeEq ){
    for( std::map< Node, bool >::iterator it = d_phase_reqs.begin(); it != d_phase_reqs.end(); ++it ){
      Trace("inst-engine-phase-req") << "   " << it->first << " -> " << it->second << std::endl;
      if (it->first.getKind() == Kind::EQUAL)
      {
        if( quantifiers::TermUtil::hasInstConstAttr(it->first[0]) ){
          if( !quantifiers::TermUtil::hasInstConstAttr(it->first[1]) ){
            d_phase_reqs_equality_term[ it->first[0] ] = it->first[1];
            d_phase_reqs_equality[ it->first[0] ] = it->second;
            Trace("inst-engine-phase-req") << "      " << it->first[0] << ( it->second ? " == " : " != " ) << it->first[1] << std::endl;
          }
        }else if( quantifiers::TermUtil::hasInstConstAttr(it->first[1]) ){
          d_phase_reqs_equality_term[ it->first[1] ] = it->first[0];
          d_phase_reqs_equality[ it->first[1] ] = it->second;
          Trace("inst-engine-phase-req") << "      " << it->first[1] << ( it->second ? " == " : " != " ) << it->first[0] << std::endl;
        }
      }
    }
  }
}

void QuantPhaseReq::computePhaseReqs( Node n, bool polarity, std::map< Node, int >& phaseReqs ){
  bool newReqPol = false;
  bool newPolarity;
  if (n.getKind() == Kind::NOT)
  {
    newReqPol = true;
    newPolarity = !polarity;
  }
  else if (n.getKind() == Kind::OR || n.getKind() == Kind::IMPLIES)
  {
    if( !polarity ){
      newReqPol = true;
      newPolarity = false;
    }
  }
  else if (n.getKind() == Kind::AND)
  {
    if( polarity ){
      newReqPol = true;
      newPolarity = true;
    }
  }
  else
  {
    int val = polarity ? 1 : -1;
    if( phaseReqs.find( n )==phaseReqs.end() ){
      phaseReqs[n] = val;
    }else if( val!=phaseReqs[n] ){
      phaseReqs[n] = 0;
    }
  }
  if( newReqPol ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if (n.getKind() == Kind::IMPLIES && i == 0)
      {
        computePhaseReqs( n[i], !newPolarity, phaseReqs );
      }
      else
      {
        computePhaseReqs( n[i], newPolarity, phaseReqs );
      }
    }
  }
}

void QuantPhaseReq::getPolarity(
    Node n, size_t child, bool hasPol, bool pol, bool& newHasPol, bool& newPol)
{
  if (n.getKind() == Kind::AND || n.getKind() == Kind::OR
      || n.getKind() == Kind::SEP_STAR)
  {
    newHasPol = hasPol;
    newPol = pol;
  }
  else if (n.getKind() == Kind::IMPLIES)
  {
    newHasPol = hasPol;
    newPol = child==0 ? !pol : pol;
  }
  else if (n.getKind() == Kind::NOT)
  {
    newHasPol = hasPol;
    newPol = !pol;
  }
  else if (n.getKind() == Kind::ITE)
  {
    newHasPol = (child!=0) && hasPol;
    newPol = pol;
  }
  else if (n.getKind() == Kind::FORALL)
  {
    newHasPol = (child==1) && hasPol;
    newPol = pol;
  }
  else
  {
    newHasPol = false;
    newPol = false;
  }
}

void QuantPhaseReq::getEntailPolarity(
    Node n, size_t child, bool hasPol, bool pol, bool& newHasPol, bool& newPol)
{
  if (n.getKind() == Kind::AND || n.getKind() == Kind::OR
      || n.getKind() == Kind::SEP_STAR)
  {
    newHasPol = hasPol && pol != (n.getKind() == Kind::OR);
    newPol = pol;
  }
  else if (n.getKind() == Kind::IMPLIES)
  {
    newHasPol = hasPol && !pol;
    newPol = child==0 ? !pol : pol;
  }
  else if (n.getKind() == Kind::NOT)
  {
    newHasPol = hasPol;
    newPol = !pol;
  }
  else
  {
    newHasPol = false;
    newPol = false;
  }
}

}  // namespace theory
}  // namespace cvc5::internal
