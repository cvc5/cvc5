/*********************                                                        */
/*! \file divisible.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
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

#include "cvc4_public.h"

#ifndef __CVC4__DIVISIBLE_H
#define __CVC4__DIVISIBLE_H

#include <iostream>
#include "util/integer.h"
#include "util/exception.h"

namespace CVC4 {

/**
 * The structure representing the divisibility-by-k predicate.
 */
struct CVC4_PUBLIC Divisible {
  const Integer k;

  Divisible(const Integer& n);

  bool operator==(const Divisible& d) const {
    return k == d.k;
  }

  bool operator!=(const Divisible& d) const {
    return !(*this == d);
  }
};/* struct Divisible */

/**
 * Hash function for the Divisible objects.
 */
struct CVC4_PUBLIC DivisibleHashFunction {
  size_t operator()(const Divisible& d) const {
    return d.k.hash();
  }
};/* struct DivisibleHashFunction */

inline std::ostream& operator <<(std::ostream& os, const Divisible& d) CVC4_PUBLIC;
inline std::ostream& operator <<(std::ostream& os, const Divisible& d) {
  return os << "divisible-by-" << d.k;
}

}/* CVC4 namespace */

#endif /* __CVC4__DIVISIBLE_H */
