/*********************                                                        */
/*! \file theory_arrays_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/attribute.h"
#include "theory/arrays/theory_arrays_rewriter.h"

namespace CVC4 {
namespace theory {
namespace arrays {

namespace attr {
  struct ArrayConstantMostFrequentValueTag { };
  struct ArrayConstantMostFrequentValueCountTag { };
}/* CVC4::theory::arrays::attr namespace */

typedef expr::Attribute<attr::ArrayConstantMostFrequentValueCountTag, uint64_t> ArrayConstantMostFrequentValueCountAttr;
typedef expr::Attribute<attr::ArrayConstantMostFrequentValueTag, Node> ArrayConstantMostFrequentValueAttr;

Node getMostFrequentValue(TNode store) {
  return store.getAttribute(ArrayConstantMostFrequentValueAttr());
}
uint64_t getMostFrequentValueCount(TNode store) {
  return store.getAttribute(ArrayConstantMostFrequentValueCountAttr());
}

void setMostFrequentValue(TNode store, TNode value) {
  return store.setAttribute(ArrayConstantMostFrequentValueAttr(), value);
}
void setMostFrequentValueCount(TNode store, uint64_t count) {
  return store.setAttribute(ArrayConstantMostFrequentValueCountAttr(), count);
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
