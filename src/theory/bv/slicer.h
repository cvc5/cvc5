/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitvector theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__SLICER_BV_H
#define CVC5__THEORY__BV__SLICER_BV_H

#include <string>
#include <vector>
#include "util/index.h"

namespace cvc5 {
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

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BV__SLICER_BV_H */
