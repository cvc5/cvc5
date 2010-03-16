/*********************                                                        */
/** type.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Interface for expression types 
 **/

#ifndef __CVC4__TYPE_H
#define __CVC4__TYPE_H

#include "cvc4_config.h"
#include "util/output.h"
#include "util/Assert.h"

#include <string>
#include <vector>
#include <limits.h>

namespace CVC4 {

namespace expr {
  namespace attr {
    struct TypeCleanupFcn;
  }/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

class NodeManager;

/**
 * Class encapsulating CVC4 expression types.
 */
class CVC4_PUBLIC Type {
protected:
  static const unsigned RC_MAX = UINT_MAX;

public:

  /** Comparision for equality */
  bool operator==(const Type& t) const;

  /** Comparison for disequality */
  bool operator!=(const Type& e) const;

  /** Get the name of this type. May be empty for composite types. */
  std::string getName() const;

  /** Is this the boolean type? */
  virtual bool isBoolean() const {
    return false;
  }

  /** Is this a function type? */
  virtual bool isFunction() const { 
    return false;
  }

  /** Is this a predicate type? NOTE: all predicate types are also
      function types. */
  virtual bool isPredicate() const {
    return false;
  }

  /** Is this a kind type (i.e., the type of a type)? */
  virtual bool isKind() const {
    return false;
  }

  /** Outputs a string representation of this type to the stream. */
  virtual void toStream(std::ostream& out) const {
    out << getName();
  }

protected:
  /** Create an un-named type. */
  Type();

  /** Create a type with the given name. */
  Type(std::string name);

  /** The name of the type (may be empty). */
  std::string d_name;

  /**
   * The reference count for this Type (how many times it's referred
   * to in the Type attribute table)
   */
  unsigned d_rc;

  /** Force a virtual destructor for safety. */
  virtual ~Type() {
    Assert(d_rc == RC_MAX || d_rc == 0,
           "illegal ref count %u for destructed Type", d_rc);
  }

  /** Increment the reference count */
  void inc() {
    if(d_rc != RC_MAX) {
      ++d_rc;
    }
  }

  /** Decrement the reference count */
  void dec() {
    if(d_rc != RC_MAX) {
      Assert(d_rc != 0, "illegal ref count %u for dec()", d_rc);
      --d_rc;
    }
  }

  friend class ::CVC4::NodeManager;
  friend struct ::CVC4::expr::attr::TypeCleanupFcn;
};

/**
 * Singleton class encapsulating the boolean type.
 */
class BooleanType : public Type {

public:
  /** Is this the boolean type? (Returns true.) */
  bool isBoolean() const;

  static BooleanType* getInstance();
private:

  /** Create a type associated with nodeManager. */
  BooleanType();

  /** Do-nothing private copy constructor operator, to prevent
      copy-construction. */
  BooleanType(const BooleanType&); 

  /** Destructor */
  ~BooleanType();

  /** Do-nothing private assignment operator, to prevent
     assignment. */
  BooleanType& operator=(const BooleanType&);
  
  /** The singleton instance */
  static BooleanType s_instance;
};

/**
 * Class encapsulating a function type.
 * TODO: Override == to check component types?
 */
class FunctionType : public Type {

public:
  /** Retrieve the argument types. The vector will be non-empty. */
  const std::vector<Type*> getArgTypes() const;

  /** Get the range type (i.e., the type of the result). */
  Type* getRangeType() const;
  
  /** Is this as function type? (Returns true.) */
  bool isFunction() const;

  /** Is this as predicate type? (Returns true if range is
      boolean.) */
  bool isPredicate() const;

  /** Outputs a string representation of this type to the stream,
      in the format "D -> R" or "(A, B, C) -> R". */
  void toStream(std::ostream& out) const;

private:

  /** Construct a function type associated with nodeManager,
   * given a vector of argument types and the range type.

   * @param argTypes a non-empty vector of input types
   * @param range the result type
   */
  FunctionType(const std::vector<Type*>& argTypes,
               Type* range);

  /** Destructor */
  ~FunctionType();
  
  /** The list of input types. */
  const std::vector<Type*> d_argTypes;

  /** The result type. */
  Type* d_rangeType;

  friend class NodeManager;
};


/** Class encapsulating the kind type (the type of types). 
*/
class KindType : public Type {

public:
  /** Is this the kind type? (Returns true.) */
  bool isKind() const;

  /** Get an instance of the kind type. */
  static KindType* getInstance();

private:

  KindType();

  /* Do-nothing private copy constructor, to prevent
     copy construction. */
  KindType(const KindType&); 

  /** Destructor */
  ~KindType();

  /* Do-nothing private assignment operator, to prevent
     assignment. */
  KindType& operator=(const KindType&);

  /** The singleton instance */
  static KindType s_instance;
};

/** Class encapsulating a user-defined sort. 
    TODO: Should sort be uniquely named per-nodeManager and not conflict
    with any builtins? */
class SortType : public Type {

public:
  /** Destructor */
  ~SortType();

private:
  /** Create a sort with the given name. */
  SortType(std::string name);

  friend class NodeManager;
};

/**
 * Output operator for types
 * @param out the stream to output to
 * @param e the type to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Type& t) CVC4_PUBLIC;

namespace expr {
namespace attr {

struct TypeCleanupFcn {
  static void cleanup(Type* t) {
    // reference-count the Type
    t->dec();
    if(t->d_rc == 0) {
      delete t;
    }
  }
};

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

}/* CVC4 namespace */

#endif /* __CVC4__TYPE_H */
