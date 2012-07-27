/*********************                                                        */
/*! \file theory_arrays_model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief MODEL for theory of arrays
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ARRAYS_MODEL_H
#define __CVC4__THEORY_ARRAYS_MODEL_H

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {

namespace quantifiers{
  class FirstOrderModel;
}

namespace arrays {

class ArrayModel{
protected:
  /** reference to model */
  quantifiers::FirstOrderModel* d_model;
  /** the array this model is for */
  Node d_arr;
public:
  ArrayModel(){}
  ArrayModel( Node arr, quantifiers::FirstOrderModel* m );
  ~ArrayModel() {}
public:
  /** pre-defined values */
  std::map< Node, Node > d_values;
  /** default value */
  Node d_default_value;
  /** get value, return arguments that the value depends on */
  Node getValue( Node n );
  /** set default */
  void setDefaultValue( Node v );
public:
  /** get array value */
  Node getArrayValue();
};/* class ArrayModel */

}
}
}

#endif