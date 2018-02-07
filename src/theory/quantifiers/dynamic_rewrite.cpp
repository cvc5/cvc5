/*********************                                                        */
/*! \file dynamic_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of dynamic_rewriter
 **/

#include "theory/quantifiers/dynamic_rewrite.h"

#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
DynamicRewriter::DynamicRewriter( const std::string& name, QuantifiersEngine * qe ) : 
d_qe(qe),
d_equalityEngine(qe->getUserContext(), "DynamicRewriter::" + name,true){
  d_equalityEngine.addFunctionKind(kind::APPLY_UF);
}

bool DynamicRewriter::addRewrite( Node a, Node b )
{
  if( a==b )
  {
    return false;
  }
  Assert( a==Rewriter::rewrite(a));
  Assert( b==Rewriter::rewrite(b));
  Node ar = toInternal( a );
  Node br = toInternal( b );
  
  
  
  
  
  
  
  return true;
}

Node DynamicRewriter::toInternal( Node a )
{
  std::map< Node, Node >::iterator it = d_term_to_internal.find( a );
  if( it != d_term_to_internal.end() )
  {
    return it->second; 
  }
  std::vector< Node > children;
  if( a.hasOperator() )
  {
    Node op = a.getOperator();
    if( a.getKind()!=APPLY_UF )
    {
      std::map< Node, Node >::iterator ito = d_term_to_internal.find( op );
      if( ito!=d_term_to_internal.end() )
      {
        op = ito->second;
      }
      else
      {
        
      }
    }
  }
  
  
  
  return a;
}
  
} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
