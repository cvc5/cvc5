/*********************                                                        */
/*! \file cvc4_private_library.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief #-inclusion of this file marks a header as private and generates a
 ** warning when the file is included improperly
 **
 ** #-inclusion of this file marks a header as private and generates a
 ** warning when the file is included improperly.
 **/

#ifndef CVC4_PRIVATE_LIBRARY_H
#define CVC4_PRIVATE_LIBRARY_H

#if !(defined(__BUILDING_CVC4LIB) || defined(__BUILDING_CVC4LIB_UNIT_TEST) \
      || defined(__BUILDING_CVC4PARSERLIB)                                 \
      || defined(__BUILDING_CVC4PARSERLIB_UNIT_TEST)                       \
      || defined(__BUILDING_CVC4DRIVER))
#  error A "private library" CVC4 header was included when not building the library, driver, or private unit test code.
#endif /* ! (__BUILDING_CVC4LIB || __BUILDING_CVC4LIB_UNIT_TEST || __BUILDING_CVC4PARSERLIB || __BUILDING_CVC4PARSERLIB_UNIT_TEST || __BUILDING_CVC4DRIVER) */

#include "cvc4_public.h"
#include "cvc4autoconfig.h"

#endif /* CVC4_PRIVATE_LIBRARY_H */
