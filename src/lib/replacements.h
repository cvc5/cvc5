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
 * Common header for replacement function sources.
 */

#ifndef CVC5__LIB__REPLACEMENTS_H
#define CVC5__LIB__REPLACEMENTS_H

#if (defined(__BUILDING_CVC4LIB) || defined(__BUILDING_CVC4LIB_UNIT_TEST)) && !defined(__BUILDING_STATISTICS_FOR_EXPORT)
#  include "cvc4_private.h"
#else
#  if defined(__BUILDING_CVC4PARSERLIB) || defined(__BUILDING_CVC4PARSERLIB_UNIT_TEST)
#    include "cvc4parser_private.h"
#  else
#if defined(__BUILDING_CVC4DRIVER) || defined(__BUILDING_CVC5_SYSTEM_TEST) \
    || defined(__BUILDING_STATISTICS_FOR_EXPORT)
#      include "cvc4autoconfig.h"
#    else
#      error Must be building libcvc4 or libcvc4parser to use replacement functions.  This is because replacement function headers should never be publicly-depended upon, as they should not be installed on user machines with 'make install'.
#    endif
#  endif
#endif

#endif /* CVC5__LIB__REPLACEMENTS_H */
