/*********************                                                        */
/** type.h
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Interface for expression types
 **/

#include "cvc4_public.h"

#ifndef __CVC4__TYPE_H
#define __CVC4__TYPE_H

#include "util/output.h"
#include "util/Assert.h"

#include <string>
#include <vector>
#include <limits.h>
#include <stdint.h>

namespace CVC4 {

class NodeManager;
template <bool ref_count> class NodeTemplate;

class BooleanType;
class FunctionType;
class KindType;
class SortType;

/**
 * Class encapsulating CVC4 expression types.
 */
class CVC4_PUBLIC Type {

  friend class NodeManager;

protected:

  /** The internal expression representation */
  NodeTemplate<true>* d_typeNode;

  /** The responsible expression manager */
  NodeManager* d_nodeManager;

  /**
   * Construct a new type given the typeNode;
   */
  Type makeType(NodeTemplate<false> typeNode) const;

  /**
   * Constructor for internal purposes.
   * @param em the expression manager that handles this expression
   * @param node the actual expression node pointer for this type
   */
  Type(NodeManager* em, NodeTemplate<true>* typeNode);

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

  /** Copy constructor */
  Type(const Type& t);

  /** Check whether this is a null type */
  bool isNull() const;

  /** Assignment operator */
  Type& operator=(const Type& t);

  /** Comparison for equality */
  bool operator==(const Type& t) const;

  /** Comparison for disequality */
  bool operator!=(const Type& t) const;

  /** Is this the Boolean type? */
  bool isBoolean() const;

  /** Cast to a Boolean type */
  operator BooleanType() const;

  /** Is this a function type? */
  bool isFunction() const;

  /** Is this a predicate type? NOTE: all predicate types are also
      function types. */
  bool isPredicate() const;

  /** Cast to a function type */
  operator FunctionType() const;

  /** Is this a sort kind */
  bool isSort() const;

  /** Cast to a sort type */
  operator SortType() const;

  /** Is this a kind type (i.e., the type of a type)? */
  bool isKind() const;

  /** Cast to a kind type */
  operator KindType() const;

  /** Outputs a string representation of this type to the stream. */
  virtual void toStream(std::ostream& out) const;

};

/**
 * Singleton class encapsulating the boolean type.
 */
class CVC4_PUBLIC BooleanType : public Type {

public:

  /** Construct from the base type */
  BooleanType(const Type& type);

  /** Is this the boolean type? (Returns true.) */
  bool isBoolean() const;

  /** Just outputs BOOLEAN */
  void toStream(std::ostream& out) const;
};

/**
 * Class encapsulating a function type.
 */
class CVC4_PUBLIC FunctionType : public Type {

public:

  /** Construct from the base type */
  FunctionType(const Type& type);

  /** Get the argument types */
  std::vector<Type> getArgTypes() const;

  /** Get the range type (i.e., the type of the result). */
  Type getRangeType() const;

  /** Is this as function type? (Returns true.) */
  bool isFunction() const;

  /** Is this as predicate type? (Returns true if range is Boolean.) */
  bool isPredicate() const;

  /**
   * Outputs a string representation of this type to the stream,
   * in the format "D -> R" or "(A, B, C) -> R".
   */
  void toStream(std::ostream& out) const;

};

/**
 * Class encapsulating a user-defined sort.
 */
class CVC4_PUBLIC SortType : public Type {

public:

  /** Construct from the base type */
  SortType(const Type& type);

  /** Get the name of the sort */
  std::string getName() const;

  /** Outouts the name of the sort */
  void toStream(std::ostream& out) const;
};

/**
 * Class encapsulating the kind type (the type of types).
 */
class CVC4_PUBLIC KindType : public Type {

public:

  /** Construct from the base type */
  KindType(const Type& type);

  /** Is this the kind type? (Returns true.) */
  bool isKind() const;

};

/**
 * Output operator for types
 * @param out the stream to output to
 * @param e the type to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Type& t) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__TYPE_H */
