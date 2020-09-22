/*********************                                                        */
/*! \file type.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface for expression types.
 **
 ** Interface for expression types
 **/

#include "cvc4_public.h"

#ifndef CVC4__TYPE_H
#define CVC4__TYPE_H

#include <climits>
#include <cstdint>
#include <string>
#include <vector>

#include "util/cardinality.h"

namespace CVC4 {

class NodeManager;
class CVC4_PUBLIC ExprManager;
class CVC4_PUBLIC Expr;
class TypeNode;
struct CVC4_PUBLIC ExprManagerMapCollection;

class CVC4_PUBLIC SmtEngine;

class CVC4_PUBLIC Datatype;
class Record;

template <bool ref_count>
class NodeTemplate;

class BooleanType;
class IntegerType;
class RealType;
class StringType;
class RegExpType;
class RoundingModeType;
class BitVectorType;
class ArrayType;
class SetType;
class DatatypeType;
class ConstructorType;
class SelectorType;
class TesterType;
class FunctionType;
class SExprType;
class SortType;
class SortConstructorType;
class Type;

/** Hash function for Types */
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

namespace expr {
  TypeNode exportTypeInternal(TypeNode n, NodeManager* from, NodeManager* nm, ExprManagerMapCollection& vmap);
}/* CVC4::expr namespace */

/**
 * Class encapsulating CVC4 expression types.
 */
class CVC4_PUBLIC Type {

  friend class SmtEngine;
  friend class ExprManager;
  friend class NodeManager;
  friend class TypeNode;
  friend std::ostream& CVC4::operator<<(std::ostream& out, const Type& t);
  friend TypeNode expr::exportTypeInternal(TypeNode n, NodeManager* from, NodeManager* nm, ExprManagerMapCollection& vmap);

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
  static TypeNode* getTypeNode(const Type& t) { return t.d_typeNode; }
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
   * Is this type finite? This assumes uninterpreted sorts have infinite
   * cardinality.
   */
  bool isFinite() const;

  /**
   * Is this type interpreted as being finite.
   * If finite model finding is enabled, this assumes all uninterpreted sorts
   *   are interpreted as finite.
   */
  bool isInterpretedFinite() const;

  /**
   * Is this a well-founded type?
   */
  bool isWellFounded() const;

  /**
   * Is this a first-class type?
   *
   * First-class types are types for which:
   * (1) we handle equalities between terms of that type, and
   * (2) they are allowed to be parameters of parametric types (e.g. index or
   * element types of arrays).
   *
   * Examples of types that are not first-class include constructor types,
   * selector types, tester types, regular expressions and SExprs.
   */
  bool isFirstClass() const;

  /**
   * Is this a function-LIKE type?
   *
   * Anything function-like except arrays (e.g., datatype selectors) is
   * considered a function here. Function-like terms can not be the argument
   * or return value for any term that is function-like.
   * This is mainly to avoid higher order.
   *
   * Note that arrays are explicitly not considered function-like here.
   *
   * @return true if this is a function-like type
   */
  bool isFunctionLike() const;

  /**
   * Construct and return a ground term for this Type.  Throws an
   * exception if this type is not well-founded.
   */
  Expr mkGroundTerm() const;

  /**
   * Construct and return a ground value for this Type.  Throws an
   * exception if this type is not well-founded.
   *
   * This is the same as mkGroundTerm, but constructs a constant value instead
   * of a canonical ground term. These two notions typically coincide. However,
   * for uninterpreted sorts, they do not: mkGroundTerm returns a fresh variable
   * whereas mkValue returns an uninterpreted constant. The motivation for
   * mkGroundTerm is that unintepreted constants should never appear in lemmas.
   * The motivation for mkGroundValue is for e.g. type enumeration and model
   * construction.
   */
  Expr mkGroundValue() const;

  /**
   * Is this type a subtype of the given type?
   */
  bool isSubtypeOf(Type t) const;

  /**
   * Is this type comparable to the given type (i.e., do they share
   * a common ancestor in the subtype tree)?
   */
  bool isComparableTo(Type t) const;

  /**
   * Get the most general base type of this type.
   */
  Type getBaseType() const;

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
   * Exports this type into a different ExprManager.
   */
  Type exportTo(ExprManager* exprManager, ExprManagerMapCollection& vmap) const;

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
   * Is this the integer type?
   * @return true if the type is a integer type
   */
  bool isInteger() const;

  /**
   * Is this the real type?
   * @return true if the type is a real type
   */
  bool isReal() const;

  /**
   * Is this the string type?
   * @return true if the type is the string type
   */
  bool isString() const;

  /**
   * Is this the regexp type?
   * @return true if the type is the regexp type
   */
  bool isRegExp() const;

  /**
   * Is this the rounding mode type?
   * @return true if the type is the rounding mode type
   */
  bool isRoundingMode() const;

  /**
   * Is this the bit-vector type?
   * @return true if the type is a bit-vector type
   */
  bool isBitVector() const;

  /**
   * Is this the floating-point type?
   * @return true if the type is a floating-point type
   */
  bool isFloatingPoint() const;

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
   * Is this a tuple type?
   * @return true if the type is a tuple type
   */
  bool isTuple() const;

  /**
   * Is this a record type?
   * @return true if the type is a record type
   */
  bool isRecord() const;

  /**
   * Is this a symbolic expression type?
   * @return true if the type is a symbolic expression type
   */
  bool isSExpr() const;

  /**
   * Is this an array type?
   * @return true if the type is a array type
   */
  bool isArray() const;

  /**
   * Is this a Set type?
   * @return true if the type is a Set type
   */
  bool isSet() const;

  /**
   * Is this a Sequence type?
   * @return true if the type is a Sequence type
   */
  bool isSequence() const;

  /**
   * Is this a datatype type?
   * @return true if the type is a datatype type
   */
  bool isDatatype() const;

  /**
   * Is this a constructor type?
   * @return true if the type is a constructor type
   */
  bool isConstructor() const;

  /**
   * Is this a selector type?
   * @return true if the type is a selector type
   */
  bool isSelector() const;

  /**
   * Is this a tester type?
   * @return true if the type is a tester type
   */
  bool isTester() const;

  /**
   * Is this a sort kind?
   * @return true if this is a sort kind
   */
  bool isSort() const;

  /**
   * Is this a sort constructor kind?
   * @return true if this is a sort constructor kind
   */
  bool isSortConstructor() const;

  /**
   * Is this a predicate subtype?
   * @return true if this is a predicate subtype
   */
  // not in release 1.0
  //bool isPredicateSubtype() const;

  /**
   * Is this an integer subrange type?
   * @return true if this is an integer subrange type
   */
  //bool isSubrange() const;

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

/** Singleton class encapsulating the Boolean type. */
class CVC4_PUBLIC BooleanType : public Type {
 public:
  /** Construct from the base type */
  BooleanType(const Type& type = Type());
};/* class BooleanType */

/** Singleton class encapsulating the integer type. */
class CVC4_PUBLIC IntegerType : public Type {
 public:
  /** Construct from the base type */
  IntegerType(const Type& type = Type());
};/* class IntegerType */

/** Singleton class encapsulating the real type. */
class CVC4_PUBLIC RealType : public Type {
 public:
  /** Construct from the base type */
  RealType(const Type& type = Type());
};/* class RealType */

/** Singleton class encapsulating the string type. */
class CVC4_PUBLIC StringType : public Type {
 public:
  /** Construct from the base type */
  StringType(const Type& type);
};/* class StringType */

/** Singleton class encapsulating the string type. */
class CVC4_PUBLIC RegExpType : public Type {
 public:
  /** Construct from the base type */
  RegExpType(const Type& type);
};/* class RegExpType */

/** Singleton class encapsulating the rounding mode type. */
class CVC4_PUBLIC RoundingModeType : public Type {
 public:
  /** Construct from the base type */
  RoundingModeType(const Type& type = Type());
};/* class RoundingModeType */

/** Class encapsulating a function type. */
class CVC4_PUBLIC FunctionType : public Type {
 public:
  /** Construct from the base type */
  FunctionType(const Type& type = Type());

  /** Get the arity of the function type */
  size_t getArity() const;

  /** Get the argument types */
  std::vector<Type> getArgTypes() const;

  /** Get the range type (i.e., the type of the result). */
  Type getRangeType() const;
};/* class FunctionType */

/** Class encapsulating a sexpr type. */
class CVC4_PUBLIC SExprType : public Type {
 public:
  /** Construct from the base type */
  SExprType(const Type& type = Type());

  /** Get the constituent types */
  std::vector<Type> getTypes() const;
};/* class SExprType */

/** Class encapsulating an array type. */
class CVC4_PUBLIC ArrayType : public Type {
 public:
  /** Construct from the base type */
  ArrayType(const Type& type = Type());

  /** Get the index type */
  Type getIndexType() const;

  /** Get the constituent type */
  Type getConstituentType() const;
};/* class ArrayType */

/** Class encapsulating a set type. */
class CVC4_PUBLIC SetType : public Type {
 public:
  /** Construct from the base type */
  SetType(const Type& type = Type());

  /** Get the element type */
  Type getElementType() const;
}; /* class SetType */

/** Class encapsulating a sequence type. */
class CVC4_PUBLIC SequenceType : public Type
{
 public:
  /** Construct from the base type */
  SequenceType(const Type& type = Type());

  /** Get the element type */
  Type getElementType() const;
}; /* class SetType */

/** Class encapsulating a user-defined sort. */
class CVC4_PUBLIC SortType : public Type {
 public:
  /** Construct from the base type */
  SortType(const Type& type = Type());

  /** Get the name of the sort */
  std::string getName() const;

  /** Is this type parameterized? */
  bool isParameterized() const;

  /** Get the parameter types */
  std::vector<Type> getParamTypes() const;

};/* class SortType */

/** Class encapsulating a user-defined sort constructor. */
class CVC4_PUBLIC SortConstructorType : public Type {
 public:
  /** Construct from the base type */
  SortConstructorType(const Type& type = Type());

  /** Get the name of the sort constructor */
  std::string getName() const;

  /** Get the arity of the sort constructor */
  size_t getArity() const;

  /** Instantiate a sort using this sort constructor */
  SortType instantiate(const std::vector<Type>& params) const;

};/* class SortConstructorType */

/** Class encapsulating the bit-vector type. */
class CVC4_PUBLIC BitVectorType : public Type {
 public:
  /** Construct from the base type */
  BitVectorType(const Type& type = Type());

  /**
   * Returns the size of the bit-vector type.
   * @return the width of the bit-vector type (> 0)
   */
  unsigned getSize() const;

};/* class BitVectorType */

/** Class encapsulating the floating point type. */
class CVC4_PUBLIC FloatingPointType : public Type {
 public:
  /** Construct from the base type */
  FloatingPointType(const Type& type = Type());

  /**
   * Returns the size of the floating-point exponent type.
   * @return the width of the floating-point exponent type (> 0)
   */
  unsigned getExponentSize() const;

  /**
   * Returns the size of the floating-point significand type.
   * @return the width of the floating-point significand type (> 0)
   */
  unsigned getSignificandSize() const;

};/* class FloatingPointType */

/** Class encapsulating the datatype type */
class CVC4_PUBLIC DatatypeType : public Type {
 public:
  /** Construct from the base type */
  DatatypeType(const Type& type = Type());

  /** Is this datatype parametric? */
  bool isParametric() const;
  /**
   * Has this datatype been fully instantiated ?
   *
   * @return true if this datatype is not parametric or, if it is, it
   * has been fully instantiated
   */
  bool isInstantiated() const;

  /** Has this datatype been instantiated for parameter `n` ? */
  bool isParameterInstantiated(unsigned n) const;

  /** Get the parameter types */
  std::vector<Type> getParamTypes() const;

  /** Get the arity of the datatype constructor */
  size_t getArity() const;

  /** Instantiate a datatype using this datatype constructor */
  DatatypeType instantiate(const std::vector<Type>& params) const;

  /** Get the length of a tuple type */
  size_t getTupleLength() const;

  /** Get the constituent types of a tuple type */
  std::vector<Type> getTupleTypes() const;

};/* class DatatypeType */

/** Class encapsulating the constructor type. */
class CVC4_PUBLIC ConstructorType : public Type {
 public:
  /** Construct from the base type */
  ConstructorType(const Type& type = Type());

  /** Get the range type */
  DatatypeType getRangeType() const;

  /** Get the argument types */
  std::vector<Type> getArgTypes() const;

  /** Get the number of constructor arguments */
  size_t getArity() const;

};/* class ConstructorType */

/** Class encapsulating the Selector type. */
class CVC4_PUBLIC SelectorType : public Type {
 public:
  /** Construct from the base type */
  SelectorType(const Type& type = Type());

  /** Get the domain type for this selector (the datatype type) */
  DatatypeType getDomain() const;

  /** Get the range type for this selector (the field type) */
  Type getRangeType() const;

};/* class SelectorType */

/** Class encapsulating the Tester type. */
class CVC4_PUBLIC TesterType : public Type {
 public:
  /** Construct from the base type */
  TesterType(const Type& type = Type());

  /** Get the type that this tester tests (the datatype type) */
  DatatypeType getDomain() const;

  /**
   * Get the range type for this tester (included for sake of
   * interface completeness), but doesn't give useful information).
   */
  BooleanType getRangeType() const;

};/* class TesterType */

}/* CVC4 namespace */

#endif /* CVC4__TYPE_H */
