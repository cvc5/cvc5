/*********************                                                        */
/*! \file quant_util.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifier utilities
 **/

#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {

QuantifiersModule::QEffort QuantifiersModule::needsModel(Theory::Effort e)
{
  return QEFFORT_NONE;
}

eq::EqualityEngine* QuantifiersModule::getEqualityEngine() const
{
  return d_quantEngine->getMasterEqualityEngine();
}

bool QuantifiersModule::areEqual(TNode n1, TNode n2) const
{
  return d_quantEngine->getEqualityQuery()->areEqual( n1, n2 );
}

bool QuantifiersModule::areDisequal(TNode n1, TNode n2) const
{
  return d_quantEngine->getEqualityQuery()->areDisequal( n1, n2 );
}

TNode QuantifiersModule::getRepresentative(TNode n) const
{
  return d_quantEngine->getEqualityQuery()->getRepresentative( n );
}

QuantifiersEngine* QuantifiersModule::getQuantifiersEngine() const
{
  return d_quantEngine;
}

quantifiers::TermDb* QuantifiersModule::getTermDatabase() const
{
  return d_quantEngine->getTermDatabase();
}

quantifiers::TermUtil* QuantifiersModule::getTermUtil() const
{
  return d_quantEngine->getTermUtil();
}

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
  Debug("inst-engine-phase-req") << "Phase requirements for " << n << ":" << std::endl;
  //now, compute if any patterns are equality required
  if( computeEq ){
    for( std::map< Node, bool >::iterator it = d_phase_reqs.begin(); it != d_phase_reqs.end(); ++it ){
      Debug("inst-engine-phase-req") << "   " << it->first << " -> " << it->second << std::endl;
      if( it->first.getKind()==EQUAL ){
        if( quantifiers::TermUtil::hasInstConstAttr(it->first[0]) ){
          if( !quantifiers::TermUtil::hasInstConstAttr(it->first[1]) ){
            d_phase_reqs_equality_term[ it->first[0] ] = it->first[1];
            d_phase_reqs_equality[ it->first[0] ] = it->second;
            Debug("inst-engine-phase-req") << "      " << it->first[0] << ( it->second ? " == " : " != " ) << it->first[1] << std::endl;
          }
        }else if( quantifiers::TermUtil::hasInstConstAttr(it->first[1]) ){
          d_phase_reqs_equality_term[ it->first[1] ] = it->first[0];
          d_phase_reqs_equality[ it->first[1] ] = it->second;
          Debug("inst-engine-phase-req") << "      " << it->first[1] << ( it->second ? " == " : " != " ) << it->first[0] << std::endl;
        }
      }
    }
  }
}

void QuantPhaseReq::computePhaseReqs( Node n, bool polarity, std::map< Node, int >& phaseReqs ){
  bool newReqPol = false;
  bool newPolarity;
  if( n.getKind()==NOT ){
    newReqPol = true;
    newPolarity = !polarity;
  }else if( n.getKind()==OR || n.getKind()==IMPLIES ){
    if( !polarity ){
      newReqPol = true;
      newPolarity = false;
    }
  }else if( n.getKind()==AND ){
    if( polarity ){
      newReqPol = true;
      newPolarity = true;
    }
  }else{
    int val = polarity ? 1 : -1;
    if( phaseReqs.find( n )==phaseReqs.end() ){
      phaseReqs[n] = val;
    }else if( val!=phaseReqs[n] ){
      phaseReqs[n] = 0;
    }
  }
  if( newReqPol ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n.getKind()==IMPLIES && i==0 ){
        computePhaseReqs( n[i], !newPolarity, phaseReqs );
      }else{
        computePhaseReqs( n[i], newPolarity, phaseReqs );
      }
    }
  }
}

void QuantPhaseReq::getPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol ) {
  if( n.getKind()==AND || n.getKind()==OR || n.getKind()==SEP_STAR ){
    newHasPol = hasPol;
    newPol = pol;
  }else if( n.getKind()==IMPLIES ){
    newHasPol = hasPol;
    newPol = child==0 ? !pol : pol;
  }else if( n.getKind()==NOT ){
    newHasPol = hasPol;
    newPol = !pol;
  }else if( n.getKind()==ITE ){
    newHasPol = (child!=0) && hasPol;
    newPol = pol;
  }else if( n.getKind()==FORALL ){
    newHasPol = (child==1) && hasPol;
    newPol = pol;
  }else{
    newHasPol = false;
    newPol = false;
  }
}

void QuantPhaseReq::getEntailPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol ) {
  if( n.getKind()==AND || n.getKind()==OR || n.getKind()==SEP_STAR ){
    newHasPol = hasPol && pol!=( n.getKind()==OR );
    newPol = pol;
  }else if( n.getKind()==IMPLIES ){
    newHasPol = hasPol && !pol;
    newPol = child==0 ? !pol : pol;
  }else if( n.getKind()==NOT ){
    newHasPol = hasPol;
    newPol = !pol;
  }else{
    newHasPol = false;
    newPol = false;
  }
}

} /* namespace CVC4::theory */
} /* namespace CVC4 */
