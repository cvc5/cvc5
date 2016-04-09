/*********************                                                        */
/*! \file pickler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a "pickler" for expressions
 **
 ** This is a "pickler" for expressions.  It produces a binary
 ** serialization of an expression that can be converted back
 ** into an expression in the same or another ExprManager.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PICKLER_H
#define __CVC4__PICKLER_H

#include "expr/variable_type_map.h"
#include "expr/expr.h"
#include "base/exception.h"

#include <exception>
#include <stack>

namespace CVC4 {

class ExprManager;

namespace expr {
namespace pickle {

class Pickler;
class PicklerPrivate;

class PickleData;// CVC4-internal representation

class CVC4_PUBLIC Pickle {
  PickleData* d_data;
  friend class Pickler;
  friend class PicklerPrivate;
public:
  Pickle();
  Pickle(const Pickle& p);
  ~Pickle();
  Pickle& operator=(const Pickle& other);
};/* class Pickle */

class CVC4_PUBLIC PicklingException : public Exception {
public:
  PicklingException() :
    Exception("Pickling failed") {
  }
};/* class PicklingException */

class CVC4_PUBLIC Pickler {
  PicklerPrivate* d_private;

  friend class PicklerPrivate;

protected:
  virtual uint64_t variableToMap(uint64_t x) const
    throw(PicklingException) {
    return x;
  }
  virtual uint64_t variableFromMap(uint64_t x) const {
    return x;
  }

public:
  Pickler(ExprManager* em);
  virtual ~Pickler();

  /**
   * Constructs a new Pickle of the node n.
   * n must be a node allocated in the node manager specified at initialization
   * time. The new pickle has variables mapped using the VariableIDMap provided
   * at initialization.
   * TODO: Fix comment
   *
   * @return the pickle, which should be dispose()'d when you're done with it
   */
  void toPickle(Expr e, Pickle& p) throw(PicklingException);

  /**
   * Constructs a node from a Pickle.
   * This destroys the contents of the Pickle.
   * The node is created in the NodeManager getNM();
   * TODO: Fix comment
   */
  Expr fromPickle(Pickle& p);

  static void debugPickleTest(Expr e);

};/* class Pickler */

class CVC4_PUBLIC MapPickler : public Pickler {
private:
  const VarMap& d_toMap;
  const VarMap& d_fromMap;

public:
  MapPickler(ExprManager* em, const VarMap& to, const VarMap& from):
    Pickler(em),
    d_toMap(to),
    d_fromMap(from) {
  }

  virtual ~MapPickler() throw() {}

protected:

  virtual uint64_t variableToMap(uint64_t x) const
    throw(PicklingException) {
    VarMap::const_iterator i = d_toMap.find(x);
    if(i != d_toMap.end()) {
      return i->second;
    } else {
      throw PicklingException();
    }
  }

  virtual uint64_t variableFromMap(uint64_t x) const; 
};/* class MapPickler */

}/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PICKLER_H */
