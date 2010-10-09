/*********************                                                        */
/*! \file type.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters, dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

namespace CVC4 {

class NodeManager;
class ExprManager;
class TypeNode;

template <bool ref_count>
class NodeTemplate;

class BooleanType;
class IntegerType;
class RealType;
class BitVectorType;
class ArrayType;
class FunctionType;
class TupleType;
class KindType;
class SortType;
class SortConstructorType;
class Type;

/** Strategy for hashing Types */
struct CVC4_PUBLIC TypeHashStrategy {
  /** Return a hash code for type t */
  static size_t hash(const CVC4::Type& t);
};/* struct TypeHashStrategy */

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
  friend class SmtEnginePrivate;
  friend class ExprManager;
  friend class TypeNode;
  friend class TypeHashStrategy;
  friend std::ostream& operator<<(std::ostream& out, const Type& t);

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

  /**
   * Initialize from an integer. Fails if the integer is not 0.
   * NOTE: This is here purely to support the auto-initialization
   * behavior of the ANTLR3 C backend. Should be removed if future
   * versions of ANTLR fix the problem.
   */
  Type(uintptr_t n);

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
   * Substitution of Types.
   */
  Type substitute(const Type& type, const Type& replacement) const;

  /**
   * Simultaneous substitution of Types.
   */
  Type substitute(const std::vector<Type>& types,
                  const std::vector<Type>& replacements) const;

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
  BooleanType(const Type& type) throw(AssertionException);
};/* class BooleanType */

/**
 * Singleton class encapsulating the integer type.
 */
class CVC4_PUBLIC IntegerType : public Type {

public:

  /** Construct from the base type */
  IntegerType(const Type& type) throw(AssertionException);
};/* class IntegerType */

/**
 * Singleton class encapsulating the real type.
 */
class CVC4_PUBLIC RealType : public Type {

public:

  /** Construct from the base type */
  RealType(const Type& type) throw(AssertionException);
};/* class RealType */

/**
 * Class encapsulating a function type.
 */
class CVC4_PUBLIC FunctionType : public Type {

public:

  /** Construct from the base type */
  FunctionType(const Type& type) throw(AssertionException);

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
  TupleType(const Type& type) throw(AssertionException);

  /** Get the constituent types */
  std::vector<Type> getTypes() const;
};/* class TupleType */

/**
 * Class encapsulating an array type.
 */
class CVC4_PUBLIC ArrayType : public Type {

public:

  /** Construct from the base type */
  ArrayType(const Type& type) throw(AssertionException);

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
  SortType(const Type& type) throw(AssertionException);

  /** Get the name of the sort */
  std::string getName() const;
};/* class SortType */

/**
 * Class encapsulating a user-defined sort constructor.
 */
class CVC4_PUBLIC SortConstructorType : public Type {

public:

  /** Construct from the base type */
  SortConstructorType(const Type& type) throw(AssertionException);

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
  KindType(const Type& type) throw(AssertionException);
};/* class KindType */

/**
 * Class encapsulating the bit-vector type.
 */
class CVC4_PUBLIC BitVectorType : public Type {

public:

  /** Construct from the base type */
  BitVectorType(const Type& type) throw(AssertionException);

  /**
   * Returns the size of the bit-vector type.
   * @return the width of the bit-vector type (> 0)
   */
  unsigned getSize() const;
};/* class BitVectorType */

}/* CVC4 namespace */

#endif /* __CVC4__TYPE_H */
