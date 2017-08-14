/*********************                                                        */
/*! \file matcher.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a type matcher
 **
 ** A class representing a type matcher.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MATCHER_H
#define __CVC4__MATCHER_H

#include <iosfwd>
#include <vector>

#include "base/cvc4_assert.h"
#include "expr/type_node.h"

namespace CVC4 {

class Matcher {
private:
  std::vector< TypeNode > d_types;
  std::vector< TypeNode > d_match;
public:
  Matcher(){}
  Matcher( DatatypeType dt ){
    addTypesFromDatatype( dt );
  }
  ~Matcher(){}

  void addTypesFromDatatype( DatatypeType dt ){
    std::vector< Type > argTypes = dt.getParamTypes();
    addTypes( argTypes );
    Debug("typecheck-idt") << "instantiating matcher for " << dt << std::endl;
    for(unsigned i = 0; i < argTypes.size(); ++i) {
      if(dt.isParameterInstantiated(i)) {
        Debug("typecheck-idt") << "++ instantiate param " << i << " : " << d_types[i] << std::endl;
        d_match[i] = d_types[i];
      }
    }
  }
  void addType( Type t ){
    d_types.push_back( TypeNode::fromType( t ) );
    d_match.push_back( TypeNode::null() );
  }
  void addTypes( std::vector< Type > types ){
    for( int i=0; i<(int)types.size(); i++ ){
      addType( types[i] );
    }
  }

  bool doMatching( TypeNode pattern, TypeNode tn ){
    Debug("typecheck-idt") << "doMatching() : " << pattern << " : " << tn << std::endl;
    std::vector< TypeNode >::iterator i = std::find( d_types.begin(), d_types.end(), pattern );
    if( i!=d_types.end() ){
      int index = i - d_types.begin();
      if( !d_match[index].isNull() ){
        Debug("typecheck-idt") << "check subtype " << tn << " " << d_match[index] << std::endl;
        TypeNode tnn = TypeNode::leastCommonTypeNode( tn, d_match[index] );
        //recognize subtype relation
        if( !tnn.isNull() ){
          d_match[index] = tnn;
          return true;
        }else{
          return false;
        }
      }else{
        d_match[ i - d_types.begin() ] = tn;
        return true;
      }
    }else if( pattern==tn ){
      return true;
    }else if( pattern.getKind()!=tn.getKind() || pattern.getNumChildren()!=tn.getNumChildren() ){
      return false;
    }else{
      for( int i=0; i<(int)pattern.getNumChildren(); i++ ){
        if( !doMatching( pattern[i], tn[i] ) ){
          return false;
        }
      }
      return true;
    }
  }

  TypeNode getMatch( unsigned int i ){ return d_match[i]; }
  void getTypes( std::vector<Type>& types ) {
    types.clear();
    for( int i=0; i<(int)d_match.size(); i++ ){
      types.push_back( d_types[i].toType() );
    }
  }
  void getMatches( std::vector<Type>& types ) {
    types.clear();
    for( int i=0; i<(int)d_match.size(); i++ ){
      if(d_match[i].isNull()) {
        types.push_back( d_types[i].toType() );
      } else {
        types.push_back( d_match[i].toType() );
      }
    }
  }
};/* class Matcher */

}/* CVC4 namespace */

#endif /* __CVC4__MATCHER_H */
