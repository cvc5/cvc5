/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An enumerator for bitvectors
 **
 ** An enumerator for bitvectors.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/type.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class DatatypesEnumerator : public TypeEnumeratorBase<DatatypesEnumerator> {
  const Datatype& d_datatype;
  size_t d_count;
  size_t d_ctor;
  size_t d_numArgs;
  size_t *d_argDistance;
  TypeEnumerator** d_argEnumerators;

public:

  DatatypesEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase(type),
    d_datatype(DatatypeType(type.toType()).getDatatype()),
    d_count(0),
    d_ctor(0),
    d_numArgs(0),
    d_argDistance(NULL),
    d_argEnumerators(NULL) {
    for(size_t c = 0; c < d_datatype.getNumConstructors(); ++c) {
      if(d_datatype[c].getNumArgs() > d_numArgs) {
        d_numArgs = d_datatype[c].getNumArgs();
      }
    }
    d_argDistance = new size_t[d_numArgs];
    d_argEnumerators = new TypeEnumerator*[d_numArgs];
    size_t a;
    for(a = 0; a < d_datatype[0].getNumArgs(); ++a) {
      d_argDistance[a] = 0;
      d_argEnumerators[a] = new TypeEnumerator(TypeNode::fromType(d_datatype[0][a].getType()));
    }
    while(a < d_numArgs) {
      d_argDistance[a] = 0;
      d_argEnumerators[a++] = NULL;
    }
  }

  ~DatatypesEnumerator() throw() {
    delete [] d_argDistance;
    for(size_t a = 0; a < d_numArgs; ++a) {
      delete d_argEnumerators[a];
    }
    delete [] d_argEnumerators;
  }

  Node operator*() throw(NoMoreValuesException) {
    if(d_ctor < d_datatype.getNumConstructors()) {
      DatatypeConstructor ctor = d_datatype[d_ctor];
      return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, ctor.getConstructor());
    } else {
      throw NoMoreValuesException(getType());
    }
  }

  DatatypesEnumerator& operator++() throw() {
    ++d_ctor;
    return *this;
  }

};/* DatatypesEnumerator */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
