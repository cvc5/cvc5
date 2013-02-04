/*********************                                                        */
/*! \file theory_arrays_model.h
 ** \verbatim
 ** Original author: Andrew Reynolds <andrew.j.reynolds@gmail.com>
 ** Major contributors: Morgan Deters <mdeters@cs.nyu.edu>
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

class TheoryModel;

namespace arrays {

class ArrayModel{
protected:
  /** the array this model is for */
  Node d_arr;
public:
  ArrayModel(){}
  ArrayModel( Node arr, TheoryModel* m );
  ~ArrayModel() {}
public:
  /** pre-defined values */
  std::map< Node, Node > d_values;
  /** base array */
  Node d_base_arr;
  /** get value, return arguments that the value depends on */
  Node getValue( TheoryModel* m, Node i );
  /** set value */
  void setValue( TheoryModel* m, Node i, Node e );
  /** set default */
  void setDefaultArray( Node arr );
public:
  /** get array value */
  Node getArrayValue();
};/* class ArrayModel */

}
}
}

#endif