/*********************                                                        */
/*! \file slicer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Mathias Preiner
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
#include "theory/bv/slicer.h"

#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"

using namespace std; 

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * Base
 * 
 */
Base::Base(uint32_t size) 
  : d_size(size),
    d_repr(size/32 + (size % 32 == 0? 0 : 1), 0)
{
  Assert(d_size > 0);
}

void Base::sliceAt(Index index)
{
  Index vector_index = index / 32;
  if (vector_index == d_repr.size())
    return;

  Index int_index = index % 32;
  uint32_t bit_mask = 1u << int_index;
  d_repr[vector_index] = d_repr[vector_index] | bit_mask;
}

bool Base::isCutPoint (Index index) const
{
  // there is an implicit cut point at the end and begining of the bv
  if (index == d_size || index == 0)
    return true;

  Index vector_index = index / 32;
  Assert(vector_index < d_size);
  Index int_index = index % 32;
  uint32_t bit_mask = 1u << int_index;

  return (bit_mask & d_repr[vector_index]) != 0;
}

std::string Base::debugPrint() const {
  std::ostringstream os;
  os << "[";
  bool first = true; 
  for (int i = d_size - 1; i >= 0; --i) {
    if (isCutPoint(i)) {
      if (first)
        first = false;
      else
        os <<"| "; 
        
      os << i ; 
    }
  }
  os << "]"; 
  return os.str(); 
}


}  // namespace bv
}  // namespace theory
}  // namespace CVC4
