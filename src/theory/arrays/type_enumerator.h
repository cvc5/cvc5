/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An enumerator for arrays
 **
 ** An enumerator for arrays.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__TYPE_ENUMERATOR_H
#define CVC4__THEORY__ARRAYS__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class ArrayEnumerator : public TypeEnumeratorBase<ArrayEnumerator> {
  /** type properties */
  TypeEnumeratorProperties * d_tep;
  TypeEnumerator d_index;
  TypeNode d_constituentType;
  NodeManager* d_nm;
  std::vector<Node> d_indexVec;
  std::vector<TypeEnumerator*> d_constituentVec;
  bool d_finished;
  Node d_arrayConst;

 public:
  ArrayEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<ArrayEnumerator>(type),
        d_tep(tep),
        d_index(type.getArrayIndexType(), tep),
        d_constituentType(type.getArrayConstituentType()),
        d_nm(NodeManager::currentNM()),
        d_indexVec(),
        d_constituentVec(),
        d_finished(false),
        d_arrayConst()
  {
    d_indexVec.push_back(*d_index);
    d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
    d_arrayConst =
        d_nm->mkConst(ArrayStoreAll(type, (*(*d_constituentVec.back()))));
    Trace("array-type-enum") << "Array const : " << d_arrayConst << std::endl;
  }

  // An array enumerator could be large, and generally you don't want to
  // go around copying these things; but a copy ctor is presently required
  // by the TypeEnumerator framework.
  ArrayEnumerator(const ArrayEnumerator& ae)
      : TypeEnumeratorBase<ArrayEnumerator>(
            ae.d_nm->mkArrayType(ae.d_index.getType(), ae.d_constituentType)),
        d_tep(ae.d_tep),
        d_index(ae.d_index),
        d_constituentType(ae.d_constituentType),
        d_nm(ae.d_nm),
        d_indexVec(ae.d_indexVec),
        d_constituentVec(),  // copied below
        d_finished(ae.d_finished),
        d_arrayConst(ae.d_arrayConst)
  {
    for(std::vector<TypeEnumerator*>::const_iterator i =
          ae.d_constituentVec.begin(), i_end = ae.d_constituentVec.end();
        i != i_end;
        ++i) {
      d_constituentVec.push_back(new TypeEnumerator(**i));
    }
  }

  ~ArrayEnumerator() {
    while (!d_constituentVec.empty()) {
      delete d_constituentVec.back();
      d_constituentVec.pop_back();
    }
  }

  Node operator*() override
  {
    if (d_finished) {
      throw NoMoreValuesException(getType());
    }
    Node n = d_arrayConst;
    for (unsigned i = 0; i < d_indexVec.size(); ++i) {
      n = d_nm->mkNode(kind::STORE, n, d_indexVec[d_indexVec.size() - 1 - i], *(*(d_constituentVec[i])));
    }
    Trace("array-type-enum") << "operator * prerewrite: " << n << std::endl;
    n = Rewriter::rewrite(n);
    Trace("array-type-enum") << "operator * returning: " << n << std::endl;
    return n;
  }

  ArrayEnumerator& operator++() override
  {
    Trace("array-type-enum") << "operator++ called, **this = " << **this << std::endl;

    if (d_finished) {
      Trace("array-type-enum") << "operator++ finished!" << std::endl;
      return *this;
    }
    while (!d_constituentVec.empty()) {
      ++(*d_constituentVec.back());
      if (d_constituentVec.back()->isFinished()) {
        delete d_constituentVec.back();
        d_constituentVec.pop_back();
      }
      else {
        break;
      }
    }

    if (d_constituentVec.empty()) {
      ++d_index;
      if (d_index.isFinished()) {
        Trace("array-type-enum") << "operator++ finished!" << std::endl;
        d_finished = true;
        return *this;
      }
      d_indexVec.push_back(*d_index);
      d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
      ++(*d_constituentVec.back());
      if (d_constituentVec.back()->isFinished()) {
        Trace("array-type-enum") << "operator++ finished!" << std::endl;
        d_finished = true;
        return *this;
      }
    }

    while (d_constituentVec.size() < d_indexVec.size()) {
      d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
    }

    Trace("array-type-enum") << "operator++ returning, **this = " << **this << std::endl;
    return *this;
  }

  bool isFinished() override
  {
    Trace("array-type-enum") << "isFinished returning: " << d_finished << std::endl;
    return d_finished;
  }

};/* class ArrayEnumerator */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARRAYS__TYPE_ENUMERATOR_H */
