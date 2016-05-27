/*********************                                                        */
/*! \file ntuple.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Similar to std::pair<>, for triples and quadruples
 **
 ** Similar to std::pair<>, for triples and quadruples.  Once we move to c++0x, this
 ** can be removed in favor of (standard-provided) N-ary tuples.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__NTUPLE_H
#define __CVC4__NTUPLE_H

namespace CVC4 {

template <class T1, class T2, class T3>
class triple {
public:
  T1 first;
  T2 second;
  T3 third;
  triple() {}
  triple(const T1& t1, const T2& t2, const T3& t3) :
    first(t1),
    second(t2),
    third(t3) {
  }
};/* class triple<> */

template <class T1, class T2, class T3>
inline triple<T1, T2, T3>
make_triple(const T1& t1, const T2& t2, const T3& t3) {
  return triple<T1, T2, T3>(t1, t2, t3);
}/* make_triple() */

template <class T1, class T2, class T3, class T4>
class quad {
public:
  T1 first;
  T2 second;
  T3 third;
  T4 fourth;
  quad() {}
  quad(const T1& t1, const T2& t2, const T3& t3, const T4& t4) :
    first(t1),
    second(t2),
    third(t3),
    fourth(t4) {
  }
};/* class quad<> */

template <class T1, class T2, class T3, class T4>
bool operator==(const quad<T1,T2,T3,T4>& x,
                const quad<T1,T2,T3,T4>& y) {
  return (x.first==y.first   && x.second==y.second &&
          x.third == y.third && x.fourth==y.fourth);
}

template <class T1, class T2, class T3, class T4>
bool operator<(const quad<T1,T2,T3,T4>& x,
                const quad<T1,T2,T3,T4>& y) {
  if(x.first< y.first) {
    return true;
  }
  else if (x.first == y.first) {
    if(x.second < y.second) {
      return true;
    }
    else if(y.second == y.second) {
      if(x.third < y.third) {
        return true;
      }
      else if (x.fourth < y.fourth) {
        return true;
      }
    }
  }
  return false;
}

template <class T1, class T2, class T3, class T4>
inline quad<T1, T2, T3, T4>
make_quad(const T1& t1, const T2& t2, const T3& t3, const T4& t4) {
  return quad<T1, T2, T3, T4>(t1, t2, t3, t4);
}/* make_quad() */

}/* CVC4 namespace */

#endif /* __CVC4__NTUPLE_H */
