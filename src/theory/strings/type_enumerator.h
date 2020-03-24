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
 * Generic iteration over vectors of indices of a given start/end length.
 */
class WordIter
{
 public:
  /**
   * This iterator will start with words at length startLength and continue
   * indefinitely.
   */
  WordIter(uint32_t startLength);
  /**
   * This iterator will start with words at length startLength and continue
   * until length endLength.
   */
  WordIter(uint32_t startLength, uint32_t endLength);
  /** copy constructor */
  WordIter(const WordIter& witer);
  /** Get the current data */
  const std::vector<unsigned>& getData() const;
  /**
   * Increment assuming the cardinality of the alphabet is card. Notice that
   * the value of card may be different for multiple calls; the caller is
   * responsible for using this function to achieve the required result. This
   * is required for enumerating sequences where the cardinality of the
   * alphabet is not known upfront, but a lower bound can be determined.
   *
   * This method returns true if the increment was successful, otherwise we
   * are finished with this iterator.
   */
  bool increment(uint32_t card);

 private:
  /** Whether we have an end length */
  bool d_hasEndLength;
  /** The end length */
  uint32_t d_endLength;
  /** The data. */
  std::vector<unsigned> d_data;
};

/**
 * A virtual class for enumerating string-like terms, with a similar
 * interface to the one above.
 */
class SEnumLen
{
 public:
  SEnumLen(TypeNode tn, uint32_t startLength);
  SEnumLen(TypeNode tn, uint32_t startLength, uint32_t endLength);
  SEnumLen(const SEnumLen& e);
  virtual ~SEnumLen() {}
  /** Get current term */
  Node getCurrent() const;
  /** Is this enumerator finished? */
  bool isFinished() const;
  /** increment, returns true if the increment was successful. */
  virtual bool increment() = 0;

 protected:
  /** The type we are enumerating */
  TypeNode d_type;
  /** The word iterator utility */
  std::unique_ptr<WordIter> d_witer;
  /** The current term */
  Node d_curr;
};

/**
 * Enumerates string values for a given length.
 */
class StringEnumLen : public SEnumLen
{
 public:
  /** For strings */
  StringEnumLen(uint32_t startLength, uint32_t card);
  StringEnumLen(uint32_t startLength, uint32_t endLength, uint32_t card);
  /** destructor */
  ~StringEnumLen() {}
  /** increment */
  bool increment() override;

 private:
  /** The cardinality of the alphabet */
  uint32_t d_cardinality;
  /** Make the current term from d_data */
  void mkCurr();
};

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator>
{
 public:
  StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  StringEnumerator(const StringEnumerator& enumerator);
  ~StringEnumerator() {}
  /** get the current term */
  Node operator*() override;
  /** increment */
  StringEnumerator& operator++() override;
  /** is this enumerator finished? */
  bool isFinished() override;

 private:
  /** underlying string enumerator */
  StringEnumLen d_wenum;
}; /* class StringEnumerator */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
