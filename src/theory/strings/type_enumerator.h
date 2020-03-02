/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for strings
 **
 ** Enumerators for strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H
#define CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H

#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Make standard model constant
 *
 * In our string representation, we represent characters using vectors
 * of unsigned integers indicating code points for the characters of that
 * string.
 *
 * To make models user-friendly, we make unsigned integer 0 correspond to the
 * 65th character ("A") in the ASCII alphabet to make models intuitive. In
 * particular, say if we have a set of string variables that are distinct but
 * otherwise unconstrained, then the model may assign them "A", "B", "C", ...
 *
 * @param vec The code points of the string in a given model,
 * @param cardinality The cardinality of the alphabet,
 * @return A string whose characters have the code points corresponding
 * to vec in the standard model construction described above.
 */
Node makeStandardModelConstant(const std::vector<unsigned>& vec,
                               uint32_t cardinality);

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator> {
 public:
  StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  Node operator*() override { return d_curr; }
  StringEnumerator& operator++() override;
  bool isFinished() override { return d_curr.isNull(); }

 private:
  /** The cardinality of the alphabet */
  uint32_t d_cardinality;
  /** The data (index to members) */
  std::vector<unsigned> d_data;
  /** The current term */
  Node d_curr;
};/* class StringEnumerator */

/**
 * Enumerates string values for a given length.
 */
class StringEnumeratorLength {
 public:
  StringEnumeratorLength(TypeNode tn, uint32_t length, uint32_t card = 256);
  Node operator*() { return d_curr; }
  StringEnumeratorLength& operator++();
  bool isFinished() { return d_curr.isNull(); }
 private:
  /** The type we are enumerating */
  TypeNode d_type;
  /** The cardinality of the alphabet */
  uint32_t d_cardinality;
  /** The data (index to members) */
  std::vector<unsigned> d_data;
  /** The current term */
  Node d_curr;
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
