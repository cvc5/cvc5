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
 * NOTE: This is very much a stub interface!!! I'm putting this here
 * so the parser can do some very simple type differentiation, but
 * this is obviously hopelessly inadequate. -Chris
 */
class Type {
 public:
  Type() { };
  Type(ExprManager* const exprManager);
  Type(ExprManager* const exprManager, std::string name);
  virtual ~Type() { };

  bool operator==(const Type& t) const;
  bool operator!=(const Type& e) const;

  ExprManager* getExprManager() const;

  std::string getName() const;

  virtual bool isBoolean() const {
    return false;
  }

  virtual bool isFunction() const { 
    return false;
  }

  virtual bool isPredicate() const {
    return false;
  }

  virtual bool isKind() const {
    return false;
  }

  virtual void toStream(std::ostream& out) const {
    out << getName();
  }

protected:
  ExprManager* d_exprManager;
  std::string d_name;
};

class BooleanType : public Type {
 public:
  BooleanType(ExprManager* exprManager);
  ~BooleanType();
  bool isBoolean() const;
};

class FunctionType : public Type {
 public:
  FunctionType(ExprManager* exprManager, 
               const Type* domain, 
               const Type* range);
  FunctionType(ExprManager* exprManager, 
               const std::vector<const Type*>& argTypes, 
               const Type* range);
  ~FunctionType();
  const std::vector<const Type*> getArgTypes() const;
  const Type* getRangeType() const;
  bool isFunction() const;
  bool isPredicate() const;
  void toStream(std::ostream& out) const;

 private:
  std::vector<const Type*> d_argTypes;
  const Type* d_rangeType;
};

class KindType : public Type {
 public:
  KindType(ExprManager* exprManager);
  ~KindType();
  bool isKind() const;
};

class SortType : public Type {
 public:
  SortType(ExprManager* exprManager, std::string name);
  ~SortType();
};

/**
 * Output operator for types
 * @param out the stream to output to
 * @param e the type to output
 * @return the stream
 */
std::ostream& operator<<(std::ostream& out, const Type& t) CVC4_PUBLIC ;
}

#endif // __CVC4__TYPE_H
