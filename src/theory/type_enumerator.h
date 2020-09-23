/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for types
 **
 ** Enumerators for types.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__TYPE_ENUMERATOR_H
#define CVC4__THEORY__TYPE_ENUMERATOR_H

#include "base/check.h"
#include "base/exception.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {

class NoMoreValuesException : public Exception {
 public:
  NoMoreValuesException(TypeNode n)
      : Exception("No more values for type `" + n.toString() + "'")
  {
  }
};/* class NoMoreValuesException */

class TypeEnumeratorInterface {
 public:
  TypeEnumeratorInterface(TypeNode type) : d_type(type) {}

  virtual ~TypeEnumeratorInterface() {}

  /** Is this enumerator out of constants to enumerate? */
  virtual bool isFinished() = 0;

  /**
   * Get the current constant of this type.
   *
   * @throws NoMoreValuesException if no such constant exists.
   */
  virtual Node operator*() = 0;

  /** Increment the pointer to the next available constant. */
  virtual TypeEnumeratorInterface& operator++() = 0;

  /** Clone this enumerator. */
  virtual TypeEnumeratorInterface* clone() const = 0;

  /** Get the type from which we're enumerating constants. */
  TypeNode getType() const { return d_type; }

 private:
  const TypeNode d_type;
}; /* class TypeEnumeratorInterface */

// AJR: This class stores particular information that is relevant to type enumeration.
//      For finite model finding, we set d_fixed_usort=true,
//      and store the finite cardinality bounds for each uninterpreted sort encountered in the model.
class TypeEnumeratorProperties
{
public:
  TypeEnumeratorProperties() : d_fixed_usort_card(false){}
  Integer getFixedCardinality( TypeNode tn ) { return d_fixed_card[tn]; }
  bool d_fixed_usort_card;
  std::map< TypeNode, Integer > d_fixed_card;
};

template <class T>
class TypeEnumeratorBase : public TypeEnumeratorInterface {
public:

  TypeEnumeratorBase(TypeNode type) :
    TypeEnumeratorInterface(type) {
  }

  TypeEnumeratorInterface* clone() const override
  {
    return new T(static_cast<const T&>(*this));
  }

};/* class TypeEnumeratorBase */

/** Type enumerator class.
 * Enumerates values for a type.
 * Its constructor takes the type to enumerate and a pointer to a
 * TypeEnumeratorProperties class, which this type enumerator does not own.
 */
class TypeEnumerator {
  TypeEnumeratorInterface* d_te;

  static TypeEnumeratorInterface* mkTypeEnumerator(
      TypeNode type, TypeEnumeratorProperties* tep);

 public:
  TypeEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : d_te(mkTypeEnumerator(type, tep))
  {
  }

  TypeEnumerator(const TypeEnumerator& te) :
    d_te(te.d_te->clone()) {
  }
  TypeEnumerator(TypeEnumeratorInterface* te) : d_te(te){
  }
  TypeEnumerator& operator=(const TypeEnumerator& te) {
    delete d_te;
    d_te = te.d_te->clone();
    return *this;
  }

  ~TypeEnumerator() { delete d_te; }
  bool isFinished()
  {
// On Mac clang, there appears to be a code generation bug in an exception
// block here.  For now, there doesn't appear a good workaround; just disable
// assertions on that setup.
#if defined(CVC4_ASSERTIONS) && !(defined(__clang__))
    if(d_te->isFinished()) {
      try {
        **d_te;
        Assert(false) << "expected an NoMoreValuesException to be thrown";
      } catch(NoMoreValuesException&) {
        // ignore the exception, we're just asserting that it would be thrown
        //
        // This block can crash on clang 3.0 on Mac OS, perhaps related to
        // bug:  http://llvm.org/bugs/show_bug.cgi?id=13359
        //
        // Hence the #if !(defined(__APPLE__) && defined(__clang__)) above
      }
    } else {
      try {
        **d_te;
      } catch(NoMoreValuesException&) {
        Assert(false) << "didn't expect a NoMoreValuesException to be thrown";
      }
    }
#endif /* CVC4_ASSERTIONS && !(APPLE || clang) */
    return d_te->isFinished();
  }
  Node operator*()
  {
// On Mac clang, there appears to be a code generation bug in an exception
// block above (and perhaps here, too).  For now, there doesn't appear a
// good workaround; just disable assertions on that setup.
#if defined(CVC4_ASSERTIONS) && !(defined(__APPLE__) && defined(__clang__))
    try {
      Node n = **d_te;
      Assert(n.isConst());
      Assert(!isFinished());
      return n;
    } catch(NoMoreValuesException&) {
      Assert(isFinished());
      throw;
    }
#else /* CVC4_ASSERTIONS && !(APPLE || clang) */
    return **d_te;
#endif /* CVC4_ASSERTIONS && !(APPLE || clang) */
  }
  TypeEnumerator& operator++()
  {
    ++*d_te;
    return *this;
  }
  TypeEnumerator operator++(int)
  {
    TypeEnumerator te = *this;
    ++*d_te;
    return te;
  }

  TypeNode getType() const { return d_te->getType(); }
};/* class TypeEnumerator */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__TYPE_ENUMERATOR_H */
