/*********************                                                        */
/*! \file theory_sets_type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__SETS__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "theory/sets/normal_form.h"

namespace CVC4 {
namespace theory {
namespace sets {

class SetEnumerator : public TypeEnumeratorBase<SetEnumerator> {
  /** type properties */
  TypeEnumeratorProperties * d_tep;
  unsigned d_index;
  TypeNode d_constituentType;
  NodeManager* d_nm;
  std::vector<bool> d_indexVec;
  std::vector<TypeEnumerator*> d_constituentVec;
  bool d_finished;
  Node d_setConst;

public:

  SetEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<SetEnumerator>(type),
    d_tep(tep),
    d_index(0),
    d_constituentType(type.getSetElementType()),
    d_nm(NodeManager::currentNM()),
    d_indexVec(),
    d_constituentVec(),
    d_finished(false),
    d_setConst()
  {
    // d_indexVec.push_back(false);
    // d_constituentVec.push_back(new TypeEnumerator(d_constituentType));
    d_setConst = d_nm->mkConst(EmptySet(type.toType()));
  }

  // An set enumerator could be large, and generally you don't want to
  // go around copying these things; but a copy ctor is presently required
  // by the TypeEnumerator framework.
  SetEnumerator(const SetEnumerator& ae) throw() :
    TypeEnumeratorBase<SetEnumerator>(ae.d_nm->mkSetType(ae.d_constituentType)),
    d_tep(ae.d_tep),
    d_index(ae.d_index),
    d_constituentType(ae.d_constituentType),
    d_nm(ae.d_nm),
    d_indexVec(ae.d_indexVec),
    d_constituentVec(),// copied below
    d_finished(ae.d_finished),
    d_setConst(ae.d_setConst)
  {
    for(std::vector<TypeEnumerator*>::const_iterator i =
          ae.d_constituentVec.begin(), i_end = ae.d_constituentVec.end();
        i != i_end;
        ++i) {
      d_constituentVec.push_back(new TypeEnumerator(**i));
    }
  }

  ~SetEnumerator() {
    while (!d_constituentVec.empty()) {
      delete d_constituentVec.back();
      d_constituentVec.pop_back();
    }
  }

  Node operator*() throw(NoMoreValuesException) {
    if (d_finished) {
      throw NoMoreValuesException(getType());
    }

    std::vector<Node> elements;
    for(unsigned i = 0; i < d_constituentVec.size(); ++i) {
      elements.push_back(*(*(d_constituentVec[i])));
    }

    Node n = NormalForm::elementsToSet(std::set<TNode>(elements.begin(), elements.end()),
                                       getType());

    Assert(n.isConst());
    Assert(n == Rewriter::rewrite(n));

    return n;
  }

  SetEnumerator& operator++() throw() {
    Trace("set-type-enum") << "operator++ called, **this = " << **this << std::endl;

    if (d_finished) {
      Trace("set-type-enum") << "operator++ finished!" << std::endl;
      return *this;
    }

    // increment by one, at the same time deleting all elements that
    // cannot be incremented any further (note: we are keeping a set
    // -- no repetitions -- thus some trickery to know what to pop and
    // what not to.)
    if(d_index > 0) {
      Assert(d_index == d_constituentVec.size());

      Node last_pre_increment;
      last_pre_increment = *(*d_constituentVec.back());

      ++(*d_constituentVec.back());

      if (d_constituentVec.back()->isFinished()) {
        delete d_constituentVec.back();
        d_constituentVec.pop_back();

        while(!d_constituentVec.empty()) {
          Node cur_pre_increment = *(*d_constituentVec.back());
          ++(*d_constituentVec.back());
          Node cur_post_increment = *(*d_constituentVec.back());
          if(last_pre_increment == cur_post_increment) {
            delete d_constituentVec.back();
            d_constituentVec.pop_back();
            last_pre_increment = cur_pre_increment;
          } else {
            break;
          }
        }
      }
    }

    if (d_constituentVec.empty()) {
      ++d_index;
      d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
    }

    while (d_constituentVec.size() < d_index) {
      TypeEnumerator* newEnumerator =
          new TypeEnumerator(*d_constituentVec.back());
      ++(*newEnumerator);
      if (newEnumerator->isFinished()) {
        Trace("set-type-enum") << "operator++ finished!" << std::endl;
        delete newEnumerator;
        d_finished = true;
        return *this;
      }
      d_constituentVec.push_back(newEnumerator);
    }

    Trace("set-type-enum") << "operator++ returning, **this = " << **this << std::endl;
    return *this;
  }

  bool isFinished() throw() {
    Trace("set-type-enum") << "isFinished returning: " << d_finished << std::endl;
    return d_finished;
  }

};/* class SetEnumerator */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__TYPE_ENUMERATOR_H */
