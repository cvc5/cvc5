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

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator> {
  std::vector< unsigned > d_data;
  uint32_t d_cardinality;
  Node d_curr;
  void mkCurr() {
    //make constant from d_data
    d_curr = NodeManager::currentNM()->mkConst( ::CVC4::String( d_data ) );
  }

 public:
  StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<StringEnumerator>(type)
  {
    Assert(type.getKind() == kind::TYPE_CONSTANT
           && type.getConst<TypeConstant>() == STRING_TYPE);
    d_cardinality = utils::getAlphabetCardinality();
    mkCurr();
  }
  Node operator*() override { return d_curr; }
  StringEnumerator& operator++() override
  {
    bool changed = false;
    do
    {
      for (unsigned i = 0; i < d_data.size(); ++i)
      {
        if (d_data[i] + 1 < d_cardinality)
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

      if (!changed)
      {
        d_data.push_back(0);
      }
    } while (!changed);

    mkCurr();
    return *this;
  }

  bool isFinished() override { return d_curr.isNull(); }
};/* class StringEnumerator */

/**
 * Enumerates string values for a given length.
 */
class StringEnumeratorLength {
 public:
  StringEnumeratorLength(TypeNode tn, uint32_t length, uint32_t card = 256)
      : d_type(tn), d_cardinality(card)
  {
    // TODO (cvc4-projects #23): sequence here
    Assert(tn.isString());
    for( unsigned i=0; i<length; i++ ){
      d_data.push_back( 0 );
    }
    mkCurr();
  }

  Node operator*() { return d_curr; }
  StringEnumeratorLength& operator++() {
    bool changed = false;
    for(unsigned i=0; i<d_data.size(); ++i) {
      if( d_data[i] + 1 < d_cardinality ) {
        ++d_data[i]; changed = true;
        break;
      } else {
        d_data[i] = 0;
      }
    }

    if(!changed) {
      d_curr = Node::null();
    }else{
      mkCurr();
    }
    return *this;
  }

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
  /** Make the current term from d_data */
  void mkCurr()
  {
    d_curr = NodeManager::currentNM()->mkConst(::CVC4::String(d_data));
  }
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
