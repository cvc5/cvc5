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

#include <math.h>

#include <vector>
#include <list>
#include <unordered_map>

#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/index.h"
#include "util/statistics_registry.h"

#ifndef CVC4__THEORY__BV__SLICER_BV_H
#define CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

namespace theory {
namespace bv {



typedef Index TermId;
extern const TermId UndefinedId;


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
  void sliceWith(const Base& other);
  bool isCutPoint(Index index) const;
  void diffCutPoints(const Base& other, Base& res) const;
  bool isEmpty() const;
  std::string debugPrint() const;
  Index getBitwidth() const { return d_size; }
  void clear() {
    for (unsigned i = 0; i < d_repr.size(); ++i) {
      d_repr[i] = 0; 
    }
  }
  bool operator==(const Base& other) const {
    if (other.getBitwidth() != getBitwidth())
      return false;
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
