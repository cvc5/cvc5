/*********************                                           -*- C++ -*-  */
/** attr_type.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_ATTR_TYPE_H
#define __CVC4_ATTR_TYPE_H

namespace CVC4 {

// an "attribute type" for types
// this is essentially a traits structure
class Type_attr {
public:
  enum { hash_value = 11 }; // could use typeid but then different on different machines/compiles
  typedef value_type Type;//Expr?
  static const Type_attr marker;
};

AttributeTable<Type_attr>

} /* CVC4 namespace */

#endif /* __CVC4_ATTR_TYPE_H */
