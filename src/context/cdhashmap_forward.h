/*********************                                                        */
/*! \file cdhashmap_forward.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a forward declaration header to declare the CDHashMap<>
 ** template
 **
 ** This is a forward declaration header to declare the CDHashMap<>
 ** template.  It's useful if you want to forward-declare CDHashMap<>
 ** without including the full cdhashmap.h header, for example, in a
 ** public header context.
 **
 ** For CDHashMap<> in particular, it's difficult to forward-declare it
 ** yourself, because it has a default template argument.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CONTEXT__CDHASHMAP_FORWARD_H
#define __CVC4__CONTEXT__CDHASHMAP_FORWARD_H

/// \cond internals

namespace __gnu_cxx {
  template <class Key> struct hash;
}/* __gnu_cxx namespace */

namespace CVC4 {
  namespace context {
    template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
    class CDHashMap;
  }/* CVC4::context namespace */
}/* CVC4 namespace */

/// \endcond

#endif /* __CVC4__CONTEXT__CDHASHMAP_FORWARD_H */
