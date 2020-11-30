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

#include "cvc4_public.h"

#ifndef CVC4__CONTEXT__DEFAULT_CLEAN_UP_H
#define CVC4__CONTEXT__DEFAULT_CLEAN_UP_H

namespace CVC4 {
namespace context {

template <class T>
class DefaultCleanUp
{
 public:
  void operator()(typename std::vector<T>::reference CVC4_UNUSED) const {}
};

}  // namespace context
}  // namespace CVC4

#endif /* __CVC4__CONTEXT__DEFAULT_CLEAN_UP_H */
