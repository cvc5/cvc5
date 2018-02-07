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
  
DynamicRewriter::DynamicRewriter( QuantifiersEngine * qe ) {

}

bool DynamicRewriter::addRewrite( Node a, Node b )
{
  Assert( a==Rewriter::rewrite(a));
  Assert( b==Rewriter::rewrite(b));
  Node ar = rewrite( a );
  Node br = rewrite( b );
  if( ar==br )
  {
    return false;
  }
  
  // orient
  
  
  
  
  
  
  
  return true;
}

Node DynamicRewriter::rewrite( Node a )
{
  return a;
}
  
} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
