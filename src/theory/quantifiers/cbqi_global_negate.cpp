/*********************                                                        */
/*! \file cbqi_global_negate.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cbqi_global_negate
 **/

#include "theory/quantifiers/cbqi_global_negate.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
CbqiGlobalNegate::CbqiGlobalNegate() {

}

bool CbqiGlobalNegate::simplify( std::vector< Node >& assertions, std::vector< Node >& new_assertions )
{
  NodeManager * nm = NodeManager::currentNM();
  
  bool do_negate = false;
  for( unsigned i=0; i<assertions.size(); i++ )
  {
    int do_negate_curr = shouldNegate( assertions[i] );
    if( do_negate_curr==-1 ){
      return false;
    }else if( do_negate_curr==1 ){
      do_negate = true;
    }
  }  
  
  if( do_negate ){
    if( assertions.size()>1 ){
      std::vector< Node > guards;
      TypeNode bt = nm->booleanType();
      for( unsigned i=0; i<assertions.size(); i++ ){
        Node g = nm->mkSkolem( "NG", bt, "for global negation");
        guards.push_back( g );
        assertions[i] = nm->mkNode( OR, assertions[i], g.negate() );
      }    
      new_assertions.push_back( nm->mkNode( OR, guards ) );
    }else{
      assertions[0] = assertions[0].negate();
    }
  }
  
  return do_negate;
}

int CbqiGlobalNegate::shouldNegate( Node n ) 
{
  
  return 0;
}
  
} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
