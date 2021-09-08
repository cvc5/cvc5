/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

// CVC5_UNUSED is to mark something (e.g. local variable, function)
// as being _possibly_ unused, so that the compiler generates no
// warning about it.  This might be the case for e.g. a variable
// only used in DEBUG builds.
#define CVC5_UNUSED [[maybe_unused]]
#define CVC5_NORETURN [[noreturn]]
#define CVC5_WARN_UNUSED_RESULT [[nodiscard]]

#endif /* CVC5_PUBLIC_H */
