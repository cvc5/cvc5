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
  /** The datatype we're enumerating */
  const Datatype& d_datatype;
  /** The datatype constructor we're currently enumerating */
  size_t d_ctor;
  /** The "first" constructor to consider; it's non-recursive */
  size_t d_zeroCtor;
  /** Delegate enumerators for the arguments of the current constructor */
  TypeEnumerator** d_argEnumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    d_argEnumerators = new TypeEnumerator*[d_datatype[d_ctor].getNumArgs()];
    for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
      d_argEnumerators[a] = NULL;
    }
  }

  /** Delete the delegate enumerators */
  void deleteEnumerators() {
    if(d_argEnumerators != NULL) {
      for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
        delete d_argEnumerators[a];
      }
      delete [] d_argEnumerators;
      d_argEnumerators = NULL;
    }
  }

public:

  DatatypesEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(type),
    d_datatype(DatatypeType(type.toType()).getDatatype()),
    d_ctor(0),
    d_zeroCtor(0),
    d_argEnumerators(NULL) {

    /* find the "zero" constructor (the first non-recursive one) */
    /* FIXME: this isn't sufficient for mutually-recursive datatypes! */
    while(d_zeroCtor < d_datatype.getNumConstructors()) {
      bool recursive = false;
      for(size_t a = 0; a < d_datatype[d_zeroCtor].getNumArgs() && !recursive; ++a) {
        recursive = (Node::fromExpr(d_datatype[d_zeroCtor][a].getSelector()).getType()[1] == type);
      }
      if(!recursive) {
        break;
      }
      ++d_zeroCtor;
    }

    /* start with the non-recursive constructor */
    d_ctor = d_zeroCtor;

    /* allocate space for the enumerators */
    newEnumerators();
  }

  ~DatatypesEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(d_ctor < d_datatype.getNumConstructors()) {
      DatatypeConstructor ctor = d_datatype[d_ctor];
      NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
      b << ctor.getConstructor();
      try {
        for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
          if(d_argEnumerators[a] == NULL) {
            d_argEnumerators[a] = new TypeEnumerator(Node::fromExpr(d_datatype[d_ctor][a].getSelector()).getType()[1]);
          }
          b << **d_argEnumerators[a];
        }
      } catch(NoMoreValuesException&) {
        InternalError();
      }
      return Node(b);
    } else {
      throw NoMoreValuesException(getType());
    }
  }

  DatatypesEnumerator& operator++() throw() {
    if(d_ctor < d_datatype.getNumConstructors()) {
      for(size_t a = d_datatype[d_ctor].getNumArgs(); a > 0; --a) {
        try {
          *++*d_argEnumerators[a - 1];
          return *this;
        } catch(NoMoreValuesException&) {
          *d_argEnumerators[a - 1] = TypeEnumerator(Node::fromExpr(d_datatype[d_ctor][a - 1].getSelector()).getType()[1]);
        }
      }

      // Here, we need to step from the current constructor to the next one

      // first, delete the current delegate enumerators
      deleteEnumerators();

      // Find the next constructor (only complicated by the notion of the "zero" constructor
      d_ctor = (d_ctor == d_zeroCtor) ? 0 : d_ctor + 1;
      if(d_ctor == d_zeroCtor) {
        ++d_ctor;
      }

      // If we aren't out of constructors, allocate space for the new delegate enumerators
      if(d_ctor < d_datatype.getNumConstructors()) {
        newEnumerators();
      }
    }
    return *this;
  }

  bool isFinished() throw() {
    return d_ctor >= d_datatype.getNumConstructors();
  }

};/* DatatypesEnumerator */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
