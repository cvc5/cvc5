

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDVECTOR_H
#define __CVC4__CONTEXT__CDVECTOR_H

#include "context/context.h"
#include "context/cdo.h"
#include "util/Assert.h"
#include "util/dynamic_array.h"

namespace CVC4 {
namespace context {

template <class T>
struct UpdatableElement{
public:
  T d_data;
  int d_contextLevelOfLastUpdate;

  UpdatableElement(const T& data) :
    d_data(data),
    d_contextLevelOfLastUpdate(0){
  }

  // UpdatableElement() :
  //   d_data(),
  //   d_contextLevelOfLastUpdate(0){
  // }
};

template <class T>
struct HistoryElement{
public:
  UpdatableElement<T> d_cached;
  unsigned d_index;
  HistoryElement(const UpdatableElement<T>& cache, unsigned index) :
    d_cached(cache), d_index(index)
  {}

  // HistoryElement() :
  //   d_cached(), d_index(0)
  // {}
};


/**
 * Generic context-dependent dynamic vector.
 * It provides the ability to destructively update the i'th item.
 * Note that the size of the vector never decreases.
 *
 * This is quite different than CDList<T>.
 */
template <class T>
class CDVector {
private:
  typedef DynamicArray< UpdatableElement<T> > CurrentVector;
  typedef DynamicArray< HistoryElement<T> > HistoryVector;

  Context* d_context;

  DynamicArray< UpdatableElement<T> > d_current;
  DynamicArray< HistoryElement<T> > d_history;

  CDO<unsigned> d_historySize;


private:
  void restoreConsistency() {
    Assert(d_history.size() >= d_historySize.get());
    while(d_history.size() > d_historySize.get()) {
      const HistoryElement<T>& back = d_history.back();
      d_current[back.d_index] = back.d_cached;
      d_history.pop_back();
    }
  }

  bool isConsistent() const{
    return d_history.size() == d_historySize.get();
  }

  void makeConsistent() {
    if(!isConsistent()){
      restoreConsistency();
    }
    Assert(isConsistent());
  }

public:
  CDVector(Context* c, bool callDestructor = false) :
    d_context(c),
    d_current(callDestructor),
    d_history(callDestructor),
    d_historySize(c,0){
  }

  unsigned size() const {
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
    d_current.push_back(UpdatableElement<T>(data));
  }

  /**
   * Access to the ith item in the list.
   */
  const T& operator[](unsigned i){
    return get(i);
  }

  const T& get(unsigned i) {
    Assert(i < size(), "index out of bounds in CDVector::get()");
    makeConsistent();
    return d_current[i].d_data;
  }

  void set(unsigned index, const T& data){
    Assert(index < size(), "index out of bounds in CDVector::set()");
    makeConsistent();

    if(d_current[index].d_contextLevelOfLastUpdate == d_context->getLevel() ){
      d_current[index].d_data = data;
    }else{
      d_history.push_back(HistoryElement<T>(d_current[index], index));
      d_historySize.set(d_historySize.get() + 1);

      d_current[index].d_data = data;
      d_current[index].d_contextLevelOfLastUpdate = d_context->getLevel();
    }
  }

};/* class CDVector */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDVECTOR_H */
