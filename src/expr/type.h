/*********************                                           -*- C++ -*-  */
/** type.h
 ** Original author: cconway
 ** Major contributors: none
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

#ifndef __CVC4__TYPE_H
#define __CVC4__TYPE_H

#include "cvc4_config.h"

#include <string>
#include <vector>

namespace CVC4 {

class ExprManager;

/**
 * Class encapsulating CVC4 expression types.
 */
class Type {
public:
  /** Comparision for equality */
  bool operator==(const Type& t) const;

  /** Comparison for disequality */
  bool operator!=(const Type& e) const;

  /** Get the ExprManager associated with this type. May be NULL for
      singleton types. */
  ExprManager* getExprManager() const;

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
  /** Create a type associated with exprManager. */
  Type(ExprManager* const exprManager);

  /** Create a type associated with exprManager with the given name. */
  Type(ExprManager* const exprManager, std::string name);

  /** Create a type with the given name. */
  Type(std::string name);

  /** Destructor */
  virtual ~Type() { };

  /** The associated ExprManager */
  ExprManager* d_exprManager;

  /** The name of the type (may be empty). */
  std::string d_name;
};

/**
 * Singleton class encapsulating the boolean type.
 */
class BooleanType : public Type {

public:
  static BooleanType* getInstance();

  /** Is this the boolean type? (Returns true.) */
  bool isBoolean() const;

private:
  /** Create a type associated with exprManager. */
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
  static FunctionType* getInstance(ExprManager* exprManager, 
                                   const Type* domain, 
                                   const Type* range);

  static FunctionType* getInstance(ExprManager* exprManager, 
                                   const std::vector<const Type*>& argTypes, 
                                   const Type* range);


  /** Retrieve the argument types. The vector will be non-empty. */
  const std::vector<const Type*> getArgTypes() const;

  /** Get the range type (i.e., the type of the result). */
  const Type* getRangeType() const;
  
  /** Is this as function type? (Returns true.) */
  bool isFunction() const;

  /** Is this as predicate type? (Returns true if range is
      boolean.) */
  bool isPredicate() const;

  /** Outputs a string representation of this type to the stream,
      in the format "D -> R" or "(A, B, C) -> R". */
  void toStream(std::ostream& out) const;

private:

  /** Construct a function type associated with exprManager,
      given a vector of argument types and the range type. 
      
      @param argTypes a non-empty vector of input types
      @param range the result type
  */
  FunctionType(ExprManager* exprManager, 
               const std::vector<const Type*>& argTypes, 
               const Type* range);

  /** Destructor */
  ~FunctionType();
  
  /** The list of input types. */
  const std::vector<const Type*> d_argTypes;

  /** The result type. */
  const Type* d_rangeType;

};


/** Class encapsulating the kind type (the type of types). 
    TODO: Should be a singleton per-ExprManager.
*/
class KindType : public Type {

public:

  /** Create a type associated with exprManager. */
  static KindType* getInstance();

  /** Is this the kind type? (Returns true.) */
  bool isKind() const;

private:

  /** Create a type associated with exprManager. */
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
    TODO: Should sort be uniquely named per-exprManager and not conflict
    with any builtins? */
class SortType : public Type {

public:

  /** Create a sort associated with exprManager with the given name. */
  SortType(ExprManager* exprManager, std::string name);

  /** Destructor */
  ~SortType();
};

/**
 * Output operator for types
 * @param out the stream to output to
 * @param e the type to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Type& t) CVC4_PUBLIC;

}

#endif /* __CVC4__TYPE_H */
