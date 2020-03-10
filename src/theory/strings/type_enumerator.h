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

#include <sstream>

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/type_enumerator.h"
#include "util/regexp.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** Generic iteration over vectors of indices of a given length and cardinality */
class WordIter {
 public:
  WordIter(uint32_t startLength, uint32_t card);
  WordIter(uint32_t startLength, uint32_t endLength, uint32_t card);
  /** copy constructor */
  WordIter(const WordIter& witer);
  /** Get the data */
  const std::vector<unsigned>& getData() const;
  /** increment */
  bool increment();
 private:
  /** has end length */
  bool d_hasEndLength;
  /** end length */
  uint32_t d_endLength;
  /** The cardinality of the alphabet */
  uint32_t d_cardinality;
  /** The data (index to members) */
  std::vector<unsigned> d_data;
};

/** String Enum len */
class SEnumLen
{
public:
  SEnumLen(TypeNode tn);
  virtual ~SEnumLen(){}
  SEnumLen(const SEnumLen& e);
  /** get current */
  Node getCurrent() const;
  /** Is this enumerator finished? */
  bool isFinished() const;
  /** increment */
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
class StringEnumLen : public SEnumLen {
 public:
  /** For strings */
  StringEnumLen(uint32_t startLength, uint32_t card);
  StringEnumLen(uint32_t startLength, uint32_t endLength, uint32_t card);
  /** destructor */
  ~StringEnumLen(){}
  /** increment */
  bool increment() override;
 private:
  /** Make the current term from d_data */
  void mkCurr();
};


/**
 * Enumerates sequence values for a given length.
 */
class SeqEnumLen : public SEnumLen {
 public:
  /** For sequences */
  SeqEnumLen(TypeNode tn, TypeEnumeratorProperties* tep, uint32_t startLength);
  SeqEnumLen(TypeNode tn, TypeEnumeratorProperties* tep, uint32_t startLength, uint32_t endLength);
  /** copy constructor */
  SeqEnumLen(const SeqEnumLen& wenum);
  /** destructor */
  ~SeqEnumLen(){}
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

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator>
{
 public:
  StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  StringEnumerator(const StringEnumerator& enumerator);
  ~StringEnumerator(){}
  Node operator*() override;
  StringEnumerator& operator++() override;
  bool isFinished() override;
 private:
  /** underlying string enumerator */
  StringEnumLen d_wenum;
};/* class StringEnumerator */


class SequenceEnumerator : public TypeEnumeratorBase<SequenceEnumerator>
{
 public:
  SequenceEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  SequenceEnumerator(const SequenceEnumerator& enumerator);
  ~SequenceEnumerator(){}
  Node operator*() override;
  SequenceEnumerator& operator++() override;
  bool isFinished() override;
private:
  /** underlying sequence enumerator */
  SeqEnumLen d_wenum;
}; /* class SequenceEnumerator */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
