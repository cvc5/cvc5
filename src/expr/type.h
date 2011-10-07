/*********************                                                        */
/*! \file type.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: dejan, mdeters
 ** Minor contributors (to current version): ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interface for expression types.
 **
 ** Interface for expression types
 **/

#include "cvc4_public.h"

#ifndef __CVC4__TYPE_H
#define __CVC4__TYPE_H

#include <string>
#include <vector>
#include <limits.h>
#include <stdint.h>

#include "util/Assert.h"
#include "util/cardinality.h"

namespace CVC4 {

class NodeManager;
class ExprManager;
class Expr;
class TypeNode;

class SmtEngine;

class Datatype;

template <bool ref_count>
class NodeTemplate;

class BooleanType;
class IntegerType;
class RealType;
class PseudobooleanType;
class BitVectorType;
class ArrayType;
class DatatypeType;
class ConstructorType;
class SelectorType;
class TesterType;
class FunctionType;
class TupleType;
class KindType;
class SortType;
class SortConstructorType;
class Type;

/** Strategy for hashing Types */
struct CVC4_PUBLIC TypeHashFunction {
  /** Return a hash code for type t */
  size_t operator()(const CVC4::Type& t) const;
};/* struct TypeHashFunction */

/**
 * Output operator for types
 * @param out the stream to output to
 * @param t the type to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Type& t) CVC4_PUBLIC;

/**
 * Class encapsulating CVC4 expression types.
 */
class CVC4_PUBLIC Type {

  friend class SmtEngine;
  friend class ExprManager;
  friend class NodeManager;
  friend class TypeNode;
  friend struct TypeHashStrategy;
  friend std::ostream& CVC4::operator<<(std::ostream& out, const Type& t);

protected:

  /** The internal expression representation */
  TypeNode* d_typeNode;

  /** The responsible expression manager */
  NodeManager* d_nodeManager;

  /**
   * Construct a new type given the typeNode, for internal use only.
   * @param typeNode the TypeNode to use
   * @return the Type corresponding to the TypeNode
   */
  Type makeType(const TypeNode& typeNode) const;

  /**
   * Constructor for internal purposes.
   * @param em the expression manager that handles this expression
   * @param typeNode the actual TypeNode pointer for this type
   */
  Type(NodeManager* em, TypeNode* typeNode);

  /** Accessor for derived classes */
  static TypeNode* getTypeNode(const Type& t) throw() { return t.d_typeNode; }

public:

  /** Force a virtual destructor for safety. */
  virtual ~Type();

  /** Default constructor */
  Type();

  /**
   * Copy constructor.
   * @param t the type to make a copy of
   */
  Type(const Type& t);

  /**
   * Check whether this is a null type
   * @return true if type is null
   */
  bool isNull() const;

  /**
   * Return the cardinality of this type.
   */
  Cardinality getCardinality() const;

  /**
   * Is this a well-founded type?  (I.e., do there exist ground
   * terms?)
   */
  bool isWellFounded() const;

  /**
   * Construct and return a ground term for this Type.  Throws an
   * exception if this type is not well-founded.
   */
  Expr mkGroundTerm() const;

  /**
   * Substitution of Types.
   */
  Type substitute(const Type& type, const Type& replacement) const;

  /**
   * Simultaneous substitution of Types.
   */
  Type substitute(const std::vector<Type>& types,
                  const std::vector<Type>& replacements) const;

  /**
   * Get this type's ExprManager.
   */
  ExprManager* getExprManager() const;

  /**
   * Assignment operator.
   * @param t the type to assign to this type
   * @return this type after assignment.
   */
  Type& operator=(const Type& t);

  /**
   * Comparison for structural equality.
   * @param t the type to compare to
   * @returns true if the types are equal
   */
  bool operator==(const Type& t) const;

  /**
   * Comparison for structural disequality.
   * @param t the type to compare to
   * @returns true if the types are not equal
   */
  bool operator!=(const Type& t) const;

  /**
   * An ordering on Types so they can be stored in maps, etc.
   */
  bool operator<(const Type& t) const;

  /**
   * An ordering on Types so they can be stored in maps, etc.
   */
  bool operator<=(const Type& t) const;

  /**
   * An ordering on Types so they can be stored in maps, etc.
   */
  bool operator>(const Type& t) const;

  /**
   * An ordering on Types so they can be stored in maps, etc.
   */
  bool operator>=(const Type& t) const;

  /**
   * Is this the Boolean type?
   * @return true if the type is a Boolean type
   */
  bool isBoolean() const;

  /**
   * Cast this type to a Boolean type
   * @return the BooleanType
   */
  operator BooleanType() const throw(AssertionException);

  /**
   * Is this the integer type?
   * @return true if the type is a integer type
   */
  bool isInteger() const;

  /**
   * Cast this type to a integer type
   * @return the IntegerType
   */
  operator IntegerType() const throw(AssertionException);

  /**
   * Is this the real type?
   * @return true if the type is a real type
   */
  bool isReal() const;

  /**
   * Cast this type to a real type
   * @return the RealType
   */
  operator RealType() const throw(AssertionException);

  /**
   * Is this the pseudoboolean type?
   * @return true if the type is the pseudoboolean type
   */
  bool isPseudoboolean() const;

  /**
   * Cast this type to a pseudoboolean type
   * @return the PseudobooleanType
   */
  operator PseudobooleanType() const throw(AssertionException);

  /**
   * Is this the bit-vector type?
   * @return true if the type is a bit-vector type
   */
  bool isBitVector() const;

  /**
   * Cast this type to a bit-vector type
   * @return the BitVectorType
   */
  operator BitVectorType() const throw(AssertionException);

  /**
   * Is this a function type?
   * @return true if the type is a function type
   */
  bool isFunction() const;

  /**
   * Is this a predicate type, i.e. if it's a function type mapping to Boolean.
   * All predicate types are also function types.
   * @return true if the type is a predicate type
   */
  bool isPredicate() const;

  /**
   * Cast this type to a function type
   * @return the FunctionType
   */
  operator FunctionType() const throw(AssertionException);

  /**
   * Is this a tuple type?
   * @return true if the type is a tuple type
   */
  bool isTuple() const;

  /**
   * Cast this type to a tuple type
   * @return the TupleType
   */
  operator TupleType() const throw(AssertionException);

  /**
   * Is this an array type?
   * @return true if the type is a array type
   */
  bool isArray() const;

  /**
   * Cast this type to an array type
   * @return the ArrayType
   */
  operator ArrayType() const throw(AssertionException);

  /**
   * Is this a datatype type?
   * @return true if the type is a datatype type
   */
  bool isDatatype() const;

  /**
   * Cast this type to a datatype type
   * @return the DatatypeType
   */
  operator DatatypeType() const throw(AssertionException);

  /**
   * Is this a constructor type?
   * @return true if the type is a constructor type
   */
  bool isConstructor() const;

  /**
   * Cast this type to a constructor type
   * @return the ConstructorType
   */
  operator ConstructorType() const throw(AssertionException);

  /**
   * Is this a selector type?
   * @return true if the type is a selector type
   */
  bool isSelector() const;

  /**
   * Cast this type to a selector type
   * @return the SelectorType
   */
  operator SelectorType() const throw(AssertionException);

  /**
   * Is this a tester type?
   * @return true if the type is a tester type
   */
  bool isTester() const;

  /**
   * Cast this type to a tester type
   * @return the TesterType
   */
  operator TesterType() const throw(AssertionException);

  /**
   * Is this a sort kind?
   * @return true if this is a sort kind
   */
  bool isSort() const;

  /**
   * Cast this type to a sort type
   * @return the sort type
   */
  operator SortType() const throw(AssertionException);

  /**
   * Is this a sort constructor kind?
   * @return true if this is a sort constructor kind
   */
  bool isSortConstructor() const;

  /**
   * Cast this type to a sort constructor type
   * @return the sort constructor type
   */
  operator SortConstructorType() const throw(AssertionException);

  /**
   * Is this a kind type (i.e., the type of a type)?
   * @return true if this is a kind type
   */
  bool isKind() const;

  /**
   * Cast to a kind type
   * @return the kind type
   */
  operator KindType() const throw(AssertionException);

  /**
   * Outputs a string representation of this type to the stream.
   * @param out the stream to output to
   */
  void toStream(std::ostream& out) const;

  /**
   * Constructs a string representation of this type.
   */
  std::string toString() const;
};/* class Type */

/**
 * Singleton class encapsulating the Boolean type.
 */
class CVC4_PUBLIC BooleanType : public Type {

public:

  /** Construct from the base type */
  BooleanType(const Type& type = Type()) throw(AssertionException);
};/* class BooleanType */

/**
 * Singleton class encapsulating the integer type.
 */
class CVC4_PUBLIC IntegerType : public Type {

public:

  /** Construct from the base type */
  IntegerType(const Type& type = Type()) throw(AssertionException);
};/* class IntegerType */

/**
 * Singleton class encapsulating the real type.
 */
class CVC4_PUBLIC RealType : public Type {

public:

  /** Construct from the base type */
  RealType(const Type& type = Type()) throw(AssertionException);
};/* class RealType */

/**
 * Singleton class encapsulating the pseudoboolean type.
 */
class CVC4_PUBLIC PseudobooleanType : public Type {

public:

  /** Construct from the base type */
  PseudobooleanType(const Type& type) throw(AssertionException);
};/* class PseudobooleanType */

/**
 * Class encapsulating a function type.
 */
class CVC4_PUBLIC FunctionType : public Type {

public:

  /** Construct from the base type */
  FunctionType(const Type& type = Type()) throw(AssertionException);

  /** Get the argument types */
  std::vector<Type> getArgTypes() const;

  /** Get the range type (i.e., the type of the result). */
  Type getRangeType() const;
};/* class FunctionType */

/**
 * Class encapsulating a tuple type.
 */
class CVC4_PUBLIC TupleType : public Type {

public:

  /** Construct from the base type */
  TupleType(const Type& type = Type()) throw(AssertionException);

  /** Get the constituent types */
  std::vector<Type> getTypes() const;
};/* class TupleType */

/**
 * Class encapsulating an array type.
 */
class CVC4_PUBLIC ArrayType : public Type {

public:

  /** Construct from the base type */
  ArrayType(const Type& type = Type()) throw(AssertionException);

  /** Get the index type */
  Type getIndexType() const;

  /** Get the constituent type */
  Type getConstituentType() const;
};/* class ArrayType */

/**
 * Class encapsulating a user-defined sort.
 */
class CVC4_PUBLIC SortType : public Type {

public:

  /** Construct from the base type */
  SortType(const Type& type = Type()) throw(AssertionException);

  /** Get the name of the sort */
  std::string getName() const;

  /** Is this type parameterized? */
  bool isParameterized() const;

  /** Get the parameter types */
  std::vector<Type> getParamTypes() const;

};/* class SortType */

/**
 * Class encapsulating a user-defined sort constructor.
 */
class CVC4_PUBLIC SortConstructorType : public Type {

public:

  /** Construct from the base type */
  SortConstructorType(const Type& type = Type()) throw(AssertionException);

  /** Get the name of the sort constructor */
  std::string getName() const;

  /** Get the arity of the sort constructor */
  size_t getArity() const;

  /** Instantiate a sort using this sort constructor */
  SortType instantiate(const std::vector<Type>& params) const;

};/* class SortConstructorType */

/**
 * Class encapsulating the kind type (the type of types).
 */
class CVC4_PUBLIC KindType : public Type {

public:

  /** Construct from the base type */
  KindType(const Type& type = Type()) throw(AssertionException);
};/* class KindType */

/**
 * Class encapsulating the bit-vector type.
 */
class CVC4_PUBLIC BitVectorType : public Type {

public:

  /** Construct from the base type */
  BitVectorType(const Type& type = Type()) throw(AssertionException);

  /**
   * Returns the size of the bit-vector type.
   * @return the width of the bit-vector type (> 0)
   */
  unsigned getSize() const;

};/* class BitVectorType */


/**
 * Class encapsulating the datatype type
 */
class CVC4_PUBLIC DatatypeType : public Type {

public:

  /** Construct from the base type */
  DatatypeType(const Type& type = Type()) throw(AssertionException);

  /** Get the underlying datatype */
  const Datatype& getDatatype() const;

  /** Is this datatype parametric? */
  bool isParametric() const;

  /**
   * Get the constructor operator associated to the given constructor
   * name in this datatype.
   */
  Expr getConstructor(std::string name) const;

  /**
   * Has this datatype been fully instantiated ?
   *
   * @return true if this datatype is not parametric or, if it is, it
   * has been fully instantiated
   */
  bool isInstantiated() const;

  /**
   * Has this datatype been instantiated for parameter N ?
   */
  bool isParameterInstantiated(unsigned n) const;

  /** Get the parameter types */
  std::vector<Type> getParamTypes() const;

  /** Get the arity of the datatype constructor */
  size_t getArity() const;

  /** Instantiate a datatype using this datatype constructor */
  DatatypeType instantiate(const std::vector<Type>& params) const;

};/* class DatatypeType */

/**
 * Class encapsulating the constructor type
 */
class CVC4_PUBLIC ConstructorType : public Type {

public:

  /** Construct from the base type */
  ConstructorType(const Type& type = Type()) throw(AssertionException);

  /** Get the range type */
  DatatypeType getRangeType() const;

  /** Get the argument types */
  std::vector<Type> getArgTypes() const;

  /** Get the number of constructor arguments */
  size_t getArity() const;

};/* class ConstructorType */


/**
 * Class encapsulating the Selector type
 */
class CVC4_PUBLIC SelectorType : public Type {

public:

  /** Construct from the base type */
  SelectorType(const Type& type = Type()) throw(AssertionException);

  /** Get the domain type for this selector (the datatype type) */
  DatatypeType getDomain() const;

  /** Get the range type for this selector (the field type) */
  Type getRangeType() const;

};/* class SelectorType */

/**
 * Class encapsulating the Tester type
 */
class CVC4_PUBLIC TesterType : public Type {

public:

  /** Construct from the base type */
  TesterType(const Type& type = Type()) throw(AssertionException);

  /** Get the type that this tester tests (the datatype type) */
  DatatypeType getDomain() const;

  /**
   * Get the range type for this tester (included for sake of
   * interface completeness), but doesn't give useful information).
   */
  BooleanType getRangeType() const;

};/* class TesterType */

}/* CVC4 namespace */

#endif /* __CVC4__TYPE_H */
