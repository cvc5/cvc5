/*********************                                                        */
/*! \file swig.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common swig checks and definitions
 **
 ** Common swig checks and definitions, when generating swig interfaces.
 **/

#ifndef CVC4__BINDINGS__SWIG_H
#define CVC4__BINDINGS__SWIG_H

#ifndef SWIG
#  error This file should only be included when generating swig interfaces.
#endif /* SWIG */

#if !defined(SWIG_VERSION) || SWIG_VERSION < 0x030000
#  error CVC4 bindings require swig version 3.0.0 or later, sorry.
#endif /* SWIG_VERSION */

%import "cvc4_public.h"

// swig doesn't like GCC attributes
#define __attribute__(x)

#endif /* CVC4__BINDINGS__SWIG_H */
