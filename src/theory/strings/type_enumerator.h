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

/**
 * Enumerates string values for a given length.
 */
class StringEnumeratorLength {
 public:
  /** For sequences */
  StringEnumeratorLength(TypeNode tn, TypeEnumeratorProperties* tep, uint32_t startLength);
  StringEnumeratorLength(TypeNode tn, TypeEnumeratorProperties* tep, uint32_t startLength, uint32_t endLength);
  /** For strings */
  StringEnumeratorLength(uint32_t startLength, uint32_t card);
  StringEnumeratorLength(uint32_t startLength, uint32_t endLength, uint32_t card);
  /** destructor */
  ~StringEnumeratorLength(){}
  /** dereference */
  Node operator*();
  /** increment */
  StringEnumeratorLength& operator++();
  /** Is this enumerator finished? */
  bool isFinished();
 private:
  /** The type we are enumerating */
  TypeNode d_type;
  /** The word iterator utility */
  std::unique_ptr<WordIter> d_witer;
  /** an enumerator for the elements' type */
  std::unique_ptr<TypeEnumerator> d_elementEnumerator;
  /** The domain */
  std::vector<Node> d_elementDomain;
  /** The current term */
  Node d_curr;
  /** Make the current term from d_data */
  void mkCurr();
};

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator> {
 public:
  StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  StringEnumerator(const StringEnumerator& enumerator);
  ~StringEnumerator(){}
  Node operator*() override;
  StringEnumerator& operator++() override;
  bool isFinished() override;
private:
  /** underlying string enumerator */
  StringEnumeratorLength d_strEnum;
};/* class StringEnumerator */


class SequenceEnumerator : public TypeEnumeratorBase<SequenceEnumerator>
{
 public:
  SequenceEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<SequenceEnumerator>(type),
        d_childEnum(type.getSequenceElementType())
  {
    mkCurr();
  }
  Node operator*() override { return d_curr; }
  SequenceEnumerator& operator++() override
  {
    bool changed = false;
    do
    {
      for (unsigned i = 0; i < d_data.size(); ++i)
      {
        while (!d_childEnum.isFinished()
               && d_data[i] + 1 >= d_childDomain.size())
        {
          d_childDomain.push_back(*d_childEnum);
          ++d_childEnum;
        }

        if (d_data[i] + 1 < d_childDomain.size())
        {
          ++d_data[i];
          changed = true;
          break;
        }
        else
        {
          d_data[i] = 0;
        }
      }
      // increase length
      if (!changed)
      {
        d_data.push_back(0);
      }
    } while (!changed);

    mkCurr();
    return *this;
  }

  bool isFinished() override { return d_curr.isNull(); }

 private:
  void mkCurr()
  {
    // make constant from d_data  FIXME : use sequence
    d_curr = NodeManager::currentNM()->mkConst(CVC4::String(d_data));
  }
  /** The current data */
  std::vector<unsigned> d_data;
  /** The enumerated domain so far */
  std::vector<Node> d_childDomain;
  /** The current term */
  Node d_curr;
  /** Child enumeration */
  TypeEnumerator d_childEnum;
}; /* class SequenceEnumerator */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
