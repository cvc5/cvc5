/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * This is a forward declaration header to declare the
 * CDList<> template
 *
 * It's useful if you want to forward-declare CDList<> without including the
 * full cdlist.h or cdlist_context_memory.h header, for example, in a public
 * header context, or to keep compile times low when only a forward declaration
 * is needed.
 *
 * Note that all specializations of the template should be listed
 * here as well, since different specializations are defined in
 * different headers (cdlist.h and cdlist_context_memory.h).
 * Explicitly declaring both specializations here ensure that if you
 * define one, you'll get an error if you didn't include the correct
 * header (avoiding different, incompatible instantiations in
 * different compilation units).
 */

#include "cvc5_public.h"

#ifndef CVC5__CONTEXT__CDLIST_FORWARD_H
#define CVC5__CONTEXT__CDLIST_FORWARD_H

#include <memory>

#include "context/default_clean_up.h"

/// \cond internals

namespace cvc5::context {

template <class T, class CleanUp = DefaultCleanUp<T>, class Allocator = std::allocator<T> >
class CDList;

/// \endcond

}  // namespace cvc5::context

#endif /* CVC5__CONTEXT__CDLIST_FORWARD_H */
