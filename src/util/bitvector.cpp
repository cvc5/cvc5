/*
 * bitvector.cpp
 *
 *  Created on: Apr 5, 2010
 *      Author: dejan
 */

#include "bitvector.h"

namespace CVC4 {

std::ostream& operator <<(std::ostream& os, const BitVector& bv) {
  return os << bv.toString();
}

}
