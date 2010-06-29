

#include "cvc4_private.h"


#ifndef __CVC4__THEORY__ARITH__ORDERED_BOUNDS_LIST_H
#define __CVC4__THEORY__ARITH__ORDERED_BOUNDS_LIST_H

#include "expr/node.h"
#include "util/rational.h"
#include "expr/kind.h"

#include <vector>
#include <algorithm>

namespace CVC4 {
namespace theory {
namespace arith {

struct RightHandRationalLT
{
  bool operator()(TNode s1, TNode s2) const
  {
    Assert(s1.getNumChildren() >= 2);
    Assert(s2.getNumChildren() >= 2);

    Assert(s1[1].getKind() == kind::CONST_RATIONAL);
    Assert(s2[1].getKind() == kind::CONST_RATIONAL);

    TNode rh1 = s1[1];
    TNode rh2 = s2[1];
    const Rational& c1 = rh1.getConst<Rational>();
    const Rational& c2 = rh2.getConst<Rational>();
    return c1.cmp(c2) < 0;
  }
};

struct RightHandRationalGT
{
  bool operator()(TNode s1, TNode s2) const
  {
    Assert(s1.getNumChildren() >= 2);
    Assert(s2.getNumChildren() >= 2);

    Assert(s1[1].getKind() == kind::CONST_RATIONAL);
    Assert(s2[1].getKind() == kind::CONST_RATIONAL);

    TNode rh1 = s1[1];
    TNode rh2 = s2[1];
    const Rational& c1 = rh1.getConst<Rational>();
    const Rational& c2 = rh2.getConst<Rational>();
    return c1.cmp(c2) > 0;
  }
};

/**
 * An OrderedBoundsList is a lazily sorted vector of Arithmetic constraints.
 * The intended use is for a list of rewriting arithmetic atoms.
 * An example of such a list would be [(<= x 5);(= y 78); (>= x 9)].
 *
 * Nodes are required to have a CONST_RATIONAL child as their second node.
 * Nodes are sorted in increasing order according to RightHandRationalLT.
 *
 * The lists are lazily sorted in the sense that the list is not sorted until
 * an operation to access the element is attempted.
 *
 * An append() may make the list no longer sorted.
 * After an append() operation all iterators for the list become invalid.
 */
class OrderedBoundsList {
private:
  bool d_isSorted;
  std::vector<Node> d_list;

public:
  typedef std::vector<Node>::const_iterator iterator;
  typedef std::vector<Node>::const_reverse_iterator reverse_iterator;

  /**
   * Constucts a new and empty OrderBoundsList.
   * The empty list is initially sorted.
   */
  OrderedBoundsList() : d_isSorted(true){}

  /**
   * Appends a node onto the back of the list.
   * The list may no longer be sorted.
   */
  void append(TNode n){
    Assert(n.getNumChildren() >= 2);
    Assert(n[1].getKind() == kind::CONST_RATIONAL);
    d_isSorted = false;
    d_list.push_back(n);
  }

  /** returns the size of the list */
  unsigned int size(){
    return d_list.size();
  }

  /** returns the i'th element in the sort list. This may sort the list.*/
  TNode at(unsigned int idx){
    sortIfNeeded();
    return d_list.at(idx);
  }

  /** returns true if the list is known to be sorted. */
  bool isSorted() const{
    return d_isSorted;
  }

  /** sorts the list. */
  void sort(){
    d_isSorted = true;
    std::sort(d_list.begin(), d_list.end(), RightHandRationalLT());
  }

  /**
   * returns an iterator to the list that iterates in ascending order.
   * This may sort the list.
   */
  iterator begin(){
    sortIfNeeded();
    return d_list.begin();
  }
  /**
   * returns an iterator to the end of the list when interating in ascending order.
   */
  iterator end() const{
    return d_list.end();
  }

  /**
   * returns an iterator to the list that iterates in descending order.
   * This may sort the list.
   */
  reverse_iterator rbegin(){
    sortIfNeeded();
    return d_list.rend();
  }
  /**
   * returns an iterator to the end of the list when interating in descending order.
   */
  reverse_iterator rend() const{
    return d_list.rend();
  }

  /**
   * returns an iterator to the least strict upper bound of value.
   * if the list is [(<= x 2);(>= x 80);(< y 70)]
   * then *upper_bound((< z 70)) == (>= x 80)
   *
   * This may sort the list.
   * see stl::upper_bound for more information.
   */
  iterator upper_bound(TNode value){
    sortIfNeeded();
    return std::upper_bound(begin(), end(), value, RightHandRationalLT());
  }
  /**
   * returns an iterator to the greatest lower bound of value.
   * This is bound is not strict.
   * if the list is [(<= x 2);(>= x 80);(< y 70)]
   * then *lower_bound((< z 70)) == (< y 70)
   *
   * This may sort the list.
   * see stl::upper_bound for more information.
   */
  iterator lower_bound(TNode value){
    sortIfNeeded();
    return std::lower_bound(begin(), end(), value, RightHandRationalLT());
  }
  /**
   * see OrderedBoundsList::upper_bound for more information.
   * The difference is that the iterator goes in descending order.
   */
  reverse_iterator reverse_upper_bound(TNode value){
    sortIfNeeded();
    return std::upper_bound(rbegin(), rend(), value, RightHandRationalGT());
  }
  /**
   * see OrderedBoundsList::lower_bound for more information.
   * The difference is that the iterator goes in descending order.
   */
  reverse_iterator reverse_lower_bound(TNode value){
    sortIfNeeded();
    return std::lower_bound(rbegin(), rend(), value, RightHandRationalGT());
  }

  /**
   * This is an O(n) method for searching the array to check if it contains n.
   */
  bool contains(TNode n) const {
    for(std::vector<Node>::const_iterator i = d_list.begin(); i != d_list.end(); ++i){
      if(*i == n) return true;
    }
    return false;
  }
private:
  /** Sorts the list if it is not already sorted.  */
  void sortIfNeeded(){
    if(!d_isSorted){
      sort();
    }
  }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ORDERED_BOUNDS_LIST_H */
