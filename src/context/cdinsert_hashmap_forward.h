/*********************                                                        */
/*! \file cdinsert_hashmap_forward.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a forward declaration header to declare the CDInsertHashMap<>
 ** template
 **
 ** This is a forward declaration header to declare the CDInsertHashMap<>
 ** template.  It's useful if you want to forward-declare CDInsertHashMap<>
 ** without including the full cdinsert_hashmap.h header, for example, in a
 ** public header context.
 **
 ** For CDInsertHashMap<> in particular, it's difficult to forward-declare it
 ** yourself, because it has a default template argument.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CONTEXT__CDINSERT_HASHMAP_FORWARD_H
#define __CVC4__CONTEXT__CDINSERT_HASHMAP_FORWARD_H

#include <functional>

namespace CVC4 {
namespace context {
template <class Key, class Data, class HashFcn = std::hash<Key> >
class CDInsertHashMap;
}  // namespace context
}  // namespace CVC4

#endif /* __CVC4__CONTEXT__CDINSERT_HASHMAP_FORWARD_H */
