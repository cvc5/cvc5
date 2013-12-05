/*********************                                                        */
/*! \file cdvector.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDVECTOR_H
#define __CVC4__CONTEXT__CDVECTOR_H

#include "context/context.h"
#include "context/cdlist.h"
#include "util/cvc4_assert.h"
#include <vector>


namespace CVC4 {
namespace context {


/**
 * Generic context-dependent dynamic vector.
 * This is quite different than CDList<T>.
 * It provides the ability to destructively update the i'th item.
 *
 * The back of the vector may only be popped if there have been no updates to it
 * at this context level.
 */
template <class T>
class CDVector {
private:
  static const int ImpossibleLevel = -1;

  struct UpdatableElement {
  public:
    T d_data;
    int d_contextLevelOfLastUpdate;

    UpdatableElement(const T& data) :
      d_data(data),
      d_contextLevelOfLastUpdate(ImpossibleLevel) {
    }
  };/* struct CDVector<T>::UpdatableElement */

  struct HistoryElement {
  public:
    UpdatableElement d_cached;
    size_t d_index;
    HistoryElement(const UpdatableElement& cache, size_t index) :
      d_cached(cache), d_index(index) {
    }
  };/* struct CDVector<T>::HistoryElement */

  typedef std::vector< UpdatableElement > CurrentVector;
  CurrentVector d_current;



  class HistoryListCleanUp{
  private:
    CurrentVector& d_current;
  public:
    HistoryListCleanUp(CurrentVector& current)
      : d_current(current)
    {}

    void operator()(HistoryElement* back){
      d_current[back->d_index] = back->d_cached;
    }
  };/* class CDVector<T>::HistoryListCleanUp */

  typedef CDList< HistoryElement,  HistoryListCleanUp > HistoryVector;
  HistoryVector d_history;

  Context* d_context;

public:
  CDVector(Context* c) :
    d_current(),
    d_history(c, true, HistoryListCleanUp(d_current)),
    d_context(c)
  {}

  size_t size() const {
    return d_current.size();
  }

  /**
   * Return true iff there are no valid objects in the list.
   */
  bool empty() const {
    return d_current.empty();
  }

  /**
   * Add an item to the end of the list.
   * Assigns its state at level 0 to be equal to data.
   */
  void push_back(const T& data) {
    d_current.push_back(UpdatableElement(data));
  }

  /**
   * Access to the ith item in the list.
   */
  const T& operator[](size_t i) const {
    return get(i);
  }

  const T& get(size_t i) const {
    Assert(i < size(), "index out of bounds in CDVector::get()");
    //makeConsistent();
    return d_current[i].d_data;
  }

  void set(size_t index, const T& data) {
    Assert(index < size(), "index out of bounds in CDVector::set()");
    //makeConsistent();

    if(d_current[index].d_contextLevelOfLastUpdate == d_context->getLevel()) {
      d_current[index].d_data = data;
    }else{
      d_history.push_back(HistoryElement(d_current[index], index));

      d_current[index].d_data = data;
      d_current[index].d_contextLevelOfLastUpdate = d_context->getLevel();
    }
  }

  bool hasUpdates(size_t index) const {
    Assert(index < size(), "index out of bounds in CDVector::hasUpdates()");
    return d_current[index].d_contextLevelOfLastUpdate == ImpossibleLevel;
  }

  void pop_back() {
    Assert(!empty(), "pop_back() on an empty CDVector");
    Assert(!hasUpdates(size() - 1), "popping an element with updates.");
    d_current.pop_back();
  }

};/* class CDVector<T> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDVECTOR_H */
