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
 ** \brief Implementation of enumerators for strings
 **/

#include "theory/strings/type_enumerator.h"

#include "theory/strings/theory_strings_utils.h"
#include "util/regexp.h"

namespace CVC4 {
namespace theory {
namespace strings {

Node makeStandardModelConstant(const std::vector<unsigned>& vec,
                               uint32_t cardinality)
{
  std::vector<unsigned> mvec;
  // if we contain all of the printable characters
  if (cardinality >= 255)
  {
    for (unsigned i = 0, vsize = vec.size(); i < vsize; i++)
    {
      unsigned curr = vec[i];
      // convert
      Assert(vec[i] < cardinality);
      if (vec[i] <= 61)
      {
        // first 62 printable characters [\u{65}-\u{126}]: 'A', 'B', 'C', ...
        curr = vec[i] + 65;
      }
      else if (vec[i] <= 94)
      {
        // remaining 33 printable characters [\u{32}-\u{64}]: ' ', '!', '"', ...
        curr = vec[i] - 30;
      }
      else
      {
        // the remaining characters, starting with \u{127} and wrapping around
        // the first 32 non-printable characters.
        curr = (vec[i] + 32) % cardinality;
      }
      mvec.push_back(curr);
    }
  }
  else
  {
    mvec = vec;
  }
  return NodeManager::currentNM()->mkConst(String(mvec));
}

StringEnumerator::StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<StringEnumerator>(type)
{
  Assert(type.getKind() == kind::TYPE_CONSTANT
         && type.getConst<TypeConstant>() == STRING_TYPE);
  d_cardinality = utils::getAlphabetCardinality();
  d_curr = makeStandardModelConstant(d_data, d_cardinality);
}

StringEnumerator& StringEnumerator::operator++()
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

  d_curr = makeStandardModelConstant(d_data, d_cardinality);
  return *this;
}

StringEnumeratorLength::StringEnumeratorLength(TypeNode tn,
                                               uint32_t length,
                                               uint32_t card)
    : d_type(tn), d_cardinality(card)
{
  // TODO (cvc4-projects #23): sequence here
  Assert(tn.isString());
  for (unsigned i = 0; i < length; i++)
  {
    d_data.push_back(0);
  }
  d_curr = makeStandardModelConstant(d_data, d_cardinality);
}

StringEnumeratorLength& StringEnumeratorLength::operator++()
{
  bool changed = false;
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
    d_curr = Node::null();
  }
  else
  {
    d_curr = makeStandardModelConstant(d_data, d_cardinality);
  }
  return *this;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
