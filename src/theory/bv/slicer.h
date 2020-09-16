/*********************                                                        */
/*! \file slicer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__SLICER_BV_H
#define CVC4__THEORY__BV__SLICER_BV_H

#include <string>
#include <vector>
#include "util/index.h"

namespace CVC4 {
namespace theory {
namespace bv {

/** 
 * Base
 * 
 */
class Base {
  Index d_size;
  std::vector<uint32_t> d_repr;
public:
  Base(Index size);
  void sliceAt(Index index); 
  bool isCutPoint(Index index) const;
  std::string debugPrint() const;
  bool operator==(const Base& other) const {
    if (other.d_size != d_size) return false;
    for (unsigned i = 0; i < d_repr.size(); ++i) {
      if (d_repr[i] != other.d_repr[i])
        return false;
    }
    return true; 
  }
}; 

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__BV__SLICER_BV_H */
