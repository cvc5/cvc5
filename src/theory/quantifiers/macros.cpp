/*********************                                                        */
/*! \file macros.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements quantifiers macro definitions.
 **/

#include <vector>

#include "theory/quantifiers/macros.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;
using namespace CVC4::context;

void QuantifierMacros::simplify( std::vector< Node >& assertions, bool doRewrite ){
  //first, collect macro definitions
  for( size_t i=0; i<assertions.size(); i++ ){
    if( assertions[i].getKind()==FORALL ){
      std::vector< Node > args;
      for( size_t j=0; j<assertions[i][0].getNumChildren(); j++ ){
        args.push_back( assertions[i][0][j] );
      }
      //look at the body of the quantifier for macro definition
      process( assertions[i][1], true, args, assertions[i] );
    }
  }
  //now, rewrite based on macro definitions
  for( size_t i=0; i<assertions.size(); i++ ){
    assertions[i] = simplify( assertions[i] );
  }
}

bool QuantifierMacros::containsOp( Node n, Node op ){
  if( n.getKind()==APPLY_UF ){
    if( n.getOperator()==op ){
      return true;
    }
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    if( containsOp( n[i], op ) ){
      return true;
    }
  }
  return false;
}

bool QuantifierMacros::isMacroKind( Node n, bool pol ){
  return pol && ( n.getKind()==EQUAL || n.getKind()==IFF );
}

void QuantifierMacros::process( Node n, bool pol, std::vector< Node >& args, Node f ){
  if( n.getKind()==NOT ){
    process( n[0], !pol, args, f );
  }else if( n.getKind()==AND || n.getKind()==OR || n.getKind()==IMPLIES ){
    //bool favorPol = (n.getKind()==AND)==pol;
    //conditional?
  }else if( n.getKind()==ITE ){
    //can not do anything
  }else{
    //literal case
    //only care about literals in form of (basis, definition)
    if( isMacroKind( n, pol ) ){
      for( int i=0; i<2; i++ ){
        int j = i==0 ? 1 : 0;
        //check if n[i] is the basis for a macro
        if( n[i].getKind()==APPLY_UF ){
          //make sure it doesn't occur in the potential definition
          if( !containsOp( n[j], n[i].getOperator() ) ){
            //bool usable = true;
            //for( size_j a=0; a<n[i].getNumChildren(); a++ )
            //  if( std::find( args.begin(), args.end(), n[i][a] )==args.end() ){
            //  }
            //}
            Trace("macros") << n << " is possible macro in " << f << std::endl;
          }
        }
      }
    }
  }
}

Node QuantifierMacros::simplify( Node n ){
#if 0
  std::vector< Node > children;
  bool childChanged = false;
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    Node nn = simplify( n[i] );
    children.push_back( nn );
    childChanged = childChanged || nn!=n[i];
  }
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_macro_defs.find( op )!=d_macro_defs.end() ){
      //do subsitutition
      Node ns = d_macro_defs[op].second;
      std::vector< Node > vars;
      for( size_t i = 0; i<d_macro_defs[op].first.getNumChildren(); i++ ){
        vars.push_back( d_macro_defs[op].first[i] );
      }
      ns = ns.substitute( vars.begin(), vars.end(), children.begin(), children.end() );
      return ns;
    }
  }
  if( childChanged ){
    if( n.isParameterized() ){
      std::insert( children.begin(), n.getOperator() );
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }else{
    return n;
  }
#else
  return n;
#endif
}
