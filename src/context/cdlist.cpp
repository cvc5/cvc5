/*********************                                                        */
/*! \file cdlist.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent list class (only supports append)
 **
 ** This source file implements the specializations for CDList<bool> because
 ** the underlying std::vector<bool> is a specialization of std::vector<T> that
 ** is not strictly compatible.
 **
 ** See https://en.cppreference.com/w/cpp/container/vector_bool for details
 ** about std::vector<bool>.
 **/

#include "context/cdlist.h"

namespace CVC4 {
namespace context {

template <>
void CDList<bool, DefaultCleanUp<bool> >::truncateList(const size_t size)
{
  Assert(size <= d_size);
  if (d_callCleanup)
  {
    while (d_size != size)
    {
      --d_size;
      bool b = d_list[d_size];
      d_cleanUp(&b);
    }
  }
  else
  {
    d_size = size;
  }
  d_list.erase(d_list.begin() + d_size, d_list.end());
}

template <>
const bool& CDList<bool, DefaultCleanUp<bool> >::operator[](size_t i) const
{
  Assert(i < d_size) << "index out of bounds in CDList::operator[]";
  return std::move(d_list[i]);
}

}  // namespace context
}  // namespace CVC4
