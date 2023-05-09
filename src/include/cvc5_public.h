/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Macros that should be defined everywhere during the building of
 * the libraries and driver binary, and also exported to the user.
 */

#ifndef CVC5_PUBLIC_H
#define CVC5_PUBLIC_H

#include <stddef.h>
#include <stdint.h>

// Define CVC5_PREDICT_FALSE(x) that helps the compiler predict that x will be
// false (if there is compiler support).
#ifdef __has_builtin
#if __has_builtin(__builtin_expect)
#define CVC5_PREDICT_FALSE(x) (__builtin_expect(x, false))
#define CVC5_PREDICT_TRUE(x) (__builtin_expect(x, true))
#else
#define CVC5_PREDICT_FALSE(x) x
#define CVC5_PREDICT_TRUE(x) x
#endif
#else
#define CVC5_PREDICT_FALSE(x) x
#define CVC5_PREDICT_TRUE(x) x
#endif

#define CVC5_FALLTHROUGH [[fallthrough]]

// CVC5_UNUSED is to mark something (e.g. local variable, function)
// as being _possibly_ unused, so that the compiler generates no
// warning about it.  This might be the case for e.g. a variable
// only used in DEBUG builds.
#define CVC5_UNUSED [[maybe_unused]]
#define CVC5_NORETURN [[noreturn]]
#define CVC5_WARN_UNUSED_RESULT [[nodiscard]]

#endif /* CVC5_PUBLIC_H */
