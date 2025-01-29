/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The default CleanUp class that does nothing.
 */

#include "cvc5_public.h"

#ifndef CVC5__CONTEXT__DEFAULT_CLEAN_UP_H
#define CVC5__CONTEXT__DEFAULT_CLEAN_UP_H

namespace cvc5::context {

template <class T>
class DefaultCleanUp
{
 public:
  void operator()(typename std::vector<T>::reference) const {}
};

}  // namespace cvc5 

#endif /* CVC5__CONTEXT__DEFAULT_CLEAN_UP_H */
