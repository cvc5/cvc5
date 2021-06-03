/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

/// \cond internals

namespace cvc5 {
namespace context {

template <class T>
class DefaultCleanUp {
public:
 inline void operator()(T* t CVC5_UNUSED) const {}
};

template <class T, class CleanUp = DefaultCleanUp<T>, class Allocator = std::allocator<T> >
class CDList;

/// \endcond

}  // namespace context
}  // namespace cvc5

#endif /* CVC5__CONTEXT__CDLIST_FORWARD_H */
