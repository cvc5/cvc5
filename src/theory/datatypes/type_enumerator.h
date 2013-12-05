/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
  /** type */
  TypeNode d_type;

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
    d_argEnumerators(NULL),
    d_type(type) {

    //Assert(type.isDatatype());
    Debug("te") << "datatype is datatype? " << type.isDatatype() << std::endl;
    Debug("te") << "datatype is kind " << type.getKind() << std::endl;
    Debug("te") << "datatype is " << type << std::endl;

    /* find the "zero" constructor (the first non-recursive one) */
    /* FIXME: this isn't sufficient for mutually-recursive datatypes! */
    while(d_zeroCtor < d_datatype.getNumConstructors()) {
      bool recursive = false;
      if( d_datatype.isParametric() ){
        TypeNode tn = TypeNode::fromType( d_datatype[d_zeroCtor].getSpecializedConstructorType(d_type.toType()) );
        for( unsigned i=0; i<tn.getNumChildren()-1; i++ ){
          if( tn[i]==type ){
            recursive = true;
            break;
          }
        }
      }else{
        for(size_t a = 0; a < d_datatype[d_zeroCtor].getNumArgs() && !recursive; ++a) {
          if(Node::fromExpr(d_datatype[d_zeroCtor][a].getSelector()).getType()[1] == type) {
            recursive = true;
            break;
          }
        }
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

  DatatypesEnumerator(const DatatypesEnumerator& de) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(de.getType()),
    d_datatype(de.d_datatype),
    d_ctor(de.d_ctor),
    d_zeroCtor(de.d_zeroCtor),
    d_argEnumerators(NULL),
    d_type(de.d_type) {

    if(de.d_argEnumerators != NULL) {
      newEnumerators();
      for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
        if(de.d_argEnumerators[a] != NULL) {
          d_argEnumerators[a] = new TypeEnumerator(*de.d_argEnumerators[a]);
        }
      }
    }
  }

  ~DatatypesEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(d_ctor < d_datatype.getNumConstructors()) {
      DatatypeConstructor ctor = d_datatype[d_ctor];
      NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
      Type typ;
      if( d_datatype.isParametric() ){
        typ = d_datatype[d_ctor].getSpecializedConstructorType(d_type.toType());
        b << NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                              NodeManager::currentNM()->mkConst(AscriptionType(typ)), Node::fromExpr( ctor.getConstructor() ) );
      }else{
        b << ctor.getConstructor();
      }
      try {
        for(size_t a = 0; a < d_datatype[d_ctor].getNumArgs(); ++a) {
          if(d_argEnumerators[a] == NULL) {
            if( d_datatype.isParametric() ){
              d_argEnumerators[a] = new TypeEnumerator(TypeNode::fromType( typ )[a]);
            }else{
              d_argEnumerators[a] = new TypeEnumerator(Node::fromExpr(d_datatype[d_ctor][a].getSelector()).getType()[1]);
            }
          }
          b << **d_argEnumerators[a];
        }
      } catch(NoMoreValuesException&) {
        InternalError();
      }
      Node nnn = Node(b);
      //if( nnn.getType()!=d_type || !nnn.getType().isComparableTo(d_type) ){
      //  Debug("dt-warn") << "WARNING : Enum : " << nnn << " bad type : " << nnn.getType() << " " << d_type << std::endl;
      //}
      return nnn;
    } else {
      throw NoMoreValuesException(getType());
    }
  }

  DatatypesEnumerator& operator++() throw() {
    if(d_ctor < d_datatype.getNumConstructors()) {
      for(size_t a = d_datatype[d_ctor].getNumArgs(); a > 0; --a) {
        if((++*d_argEnumerators[a - 1]).isFinished()) {
          *d_argEnumerators[a - 1] = TypeEnumerator(Node::fromExpr(d_datatype[d_ctor][a - 1].getSelector()).getType()[1]);
        } else {
          return *this;
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

class TupleEnumerator : public TypeEnumeratorBase<TupleEnumerator> {
  TypeEnumerator** d_enumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    d_enumerators = new TypeEnumerator*[getType().getNumChildren()];
    for(size_t i = 0; i < getType().getNumChildren(); ++i) {
      d_enumerators[i] = new TypeEnumerator(getType()[i]);
    }
  }

  void deleteEnumerators() throw() {
    if(d_enumerators != NULL) {
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        delete d_enumerators[i];
      }
      delete [] d_enumerators;
      d_enumerators = NULL;
    }
  }

public:

  TupleEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<TupleEnumerator>(type) {
    Assert(type.isTuple());
    newEnumerators();
  }

  TupleEnumerator(const TupleEnumerator& te) throw() :
    TypeEnumeratorBase<TupleEnumerator>(te.getType()),
    d_enumerators(NULL) {

    if(te.d_enumerators != NULL) {
      newEnumerators();
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        *d_enumerators[i] = TypeEnumerator(*te.d_enumerators[i]);
      }
    }
  }

  ~TupleEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }

    NodeBuilder<> nb(kind::TUPLE);
    for(size_t i = 0; i < getType().getNumChildren(); ++i) {
      nb << **d_enumerators[i];
    }
    return Node(nb);
  }

  TupleEnumerator& operator++() throw() {
    if(isFinished()) {
      return *this;
    }

    size_t i;
    for(i = 0; i < getType().getNumChildren(); ++i) {
      if(d_enumerators[i]->isFinished()) {
        *d_enumerators[i] = TypeEnumerator(getType()[i]);
      } else {
        ++*d_enumerators[i];
        return *this;
      }
    }

    deleteEnumerators();

    return *this;
  }

  bool isFinished() throw() {
    return d_enumerators == NULL;
  }

};/* TupleEnumerator */

class RecordEnumerator : public TypeEnumeratorBase<RecordEnumerator> {
  TypeEnumerator** d_enumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    const Record& rec = getType().getConst<Record>();
    d_enumerators = new TypeEnumerator*[rec.getNumFields()];
    for(size_t i = 0; i < rec.getNumFields(); ++i) {
      d_enumerators[i] = new TypeEnumerator(TypeNode::fromType(rec[i].second));
    }
  }

  void deleteEnumerators() throw() {
    if(d_enumerators != NULL) {
      const Record& rec = getType().getConst<Record>();
      for(size_t i = 0; i < rec.getNumFields(); ++i) {
        delete d_enumerators[i];
      }
      delete [] d_enumerators;
      d_enumerators = NULL;
    }
  }

public:

  RecordEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<RecordEnumerator>(type) {
    Assert(type.isRecord());
    newEnumerators();
  }

  RecordEnumerator(const RecordEnumerator& re) throw() :
    TypeEnumeratorBase<RecordEnumerator>(re.getType()),
    d_enumerators(NULL) {

    if(re.d_enumerators != NULL) {
      newEnumerators();
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        *d_enumerators[i] = TypeEnumerator(*re.d_enumerators[i]);
      }
    }
  }

  ~RecordEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }

    NodeBuilder<> nb(kind::RECORD);
    Debug("te") << "record enumerator: creating record of type " << getType() << std::endl;
    nb << getType();
    const Record& rec = getType().getConst<Record>();
    for(size_t i = 0; i < rec.getNumFields(); ++i) {
      Debug("te") << " - " << i << " " << std::flush << "=> " << **d_enumerators[i] << std::endl;
      nb << **d_enumerators[i];
    }
    return Node(nb);
  }

  RecordEnumerator& operator++() throw() {
    if(isFinished()) {
      return *this;
    }

    size_t i;
    const Record& rec = getType().getConst<Record>();
    for(i = 0; i < rec.getNumFields(); ++i) {
      if(d_enumerators[i]->isFinished()) {
        *d_enumerators[i] = TypeEnumerator(TypeNode::fromType(rec[i].second));
      } else {
        ++*d_enumerators[i];
        return *this;
      }
    }

    deleteEnumerators();

    return *this;
  }

  bool isFinished() throw() {
    return d_enumerators == NULL;
  }

};/* RecordEnumerator */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
