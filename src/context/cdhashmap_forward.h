/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * This is a forward declaration header to declare the CDHashMap<>
 * template
 *
 * It's useful if you want to forward-declare CDHashMap<> without including the
 * full cdhashmap.h header, for example, in a public header context.
 *
 * For CDHashMap<> in particular, it's difficult to forward-declare it
 * yourself, because it has a default template argument.
 */

#include "cvc5_public.h"

#ifndef CVC5__CONTEXT__CDHASHMAP_FORWARD_H
#define CVC5__CONTEXT__CDHASHMAP_FORWARD_H

#include <functional>

/// \cond internals

namespace cvc5 {
namespace context {
template <class Key, class Data, class HashFcn = std::hash<Key> >
class CDHashMap;
}  // namespace context
}  // namespace cvc5

/// \endcond

#endif /* CVC5__CONTEXT__CDHASHMAP_FORWARD_H */
