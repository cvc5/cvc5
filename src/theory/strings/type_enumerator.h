/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerators for strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__TYPE_ENUMERATOR_H
#define CVC5__THEORY__STRINGS__TYPE_ENUMERATOR_H

#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
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

/**
 * Enumerates sequence values for a given length.
 */
class SeqEnumLen : public SEnumLen
{
 public:
  /** For sequences */
  SeqEnumLen(TypeNode tn, TypeEnumeratorProperties* tep, uint32_t startLength);
  SeqEnumLen(TypeNode tn,
             TypeEnumeratorProperties* tep,
             uint32_t startLength,
             uint32_t endLength);
  /** copy constructor */
  SeqEnumLen(const SeqEnumLen& wenum);
  /** destructor */
  ~SeqEnumLen() {}
  /** increment */
  bool increment() override;

 private:
  /** an enumerator for the elements' type */
  std::unique_ptr<TypeEnumerator> d_elementEnumerator;
  /** The domain */
  std::vector<Node> d_elementDomain;
  /** Make the current term from d_data */
  void mkCurr();
};

/** Set of the above class */
class SEnumLenSet
{
 public:
  /** constructor */
  SEnumLenSet(TypeEnumeratorProperties* tep = nullptr);
  /** destructor */
  ~SEnumLenSet() {}
  /** Get enumerator for length, type */
  SEnumLen* getEnumerator(size_t len, TypeNode tn);

 private:
  /** an enumerator for the element's type */
  TypeEnumeratorProperties* d_tep;
  /** for each start length, type */
  std::map<std::pair<size_t, TypeNode>, std::unique_ptr<SEnumLen> > d_sels;
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

class SequenceEnumerator : public TypeEnumeratorBase<SequenceEnumerator>
{
 public:
  SequenceEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  SequenceEnumerator(const SequenceEnumerator& enumerator);
  ~SequenceEnumerator() {}
  Node operator*() override;
  SequenceEnumerator& operator++() override;
  bool isFinished() override;

 private:
  /** underlying sequence enumerator */
  SeqEnumLen d_wenum;
}; /* class SequenceEnumerator */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__TYPE_ENUMERATOR_H */
