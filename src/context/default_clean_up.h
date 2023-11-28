/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
/*********************                                                        */
/*! \file default_clean_up.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The default CleanUp class that does nothing.
 **
 **/

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
