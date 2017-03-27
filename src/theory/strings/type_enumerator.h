/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for strings
 **
 ** Enumerators for strings.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H

#include <sstream>

#include "util/regexp.h"
#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace strings {

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator> {
  std::vector< unsigned > d_data;
  unsigned d_cardinality;
  Node d_curr;
  void mkCurr() {
    //make constant from d_data
    d_curr = NodeManager::currentNM()->mkConst( ::CVC4::String( d_data ) );
  }
public:

  StringEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<StringEnumerator>(type) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == STRING_TYPE);
    d_cardinality = 256;
    mkCurr();
  }
  Node operator*() throw() {
    return d_curr;
  }
  StringEnumerator& operator++() {
  bool changed = false;
  do{
    for(unsigned i=0; i<d_data.size(); ++i) {
      if( d_data[i] + 1 < d_cardinality ) {
        ++d_data[i]; changed = true;
        break;
      } else {
        d_data[i] = 0;
      }
    }

    if(!changed) {
      d_data.push_back( 0 );
    }
  }while(!changed);

  mkCurr();
    return *this;
  }

  bool isFinished() throw() {
    return d_curr.isNull();
  }

};/* class StringEnumerator */


class StringEnumeratorLength {
private:
  unsigned d_cardinality;
  std::vector< unsigned > d_data;
  Node d_curr;
  void mkCurr() {
    //make constant from d_data
    d_curr = NodeManager::currentNM()->mkConst( ::CVC4::String( d_data ) );
  }
public:
  StringEnumeratorLength(unsigned length, unsigned card = 256) : d_cardinality(card) {
    for( unsigned i=0; i<length; i++ ){
      d_data.push_back( 0 );
    }
    mkCurr();
  }

  Node operator*() throw() {
    return d_curr;
  }

  StringEnumeratorLength& operator++() {
    bool changed = false;
    for(unsigned i=0; i<d_data.size(); ++i) {
      if( d_data[i] + 1 < d_cardinality ) {
        ++d_data[i]; changed = true;
        break;
      } else {
        d_data[i] = 0;
      }
    }

    if(!changed) {
      d_curr = Node::null();
    }else{
      mkCurr();
    }
    return *this;
  }

  bool isFinished() throw() {
    return d_curr.isNull();
  }
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
