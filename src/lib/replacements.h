/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for replacement function sources.
 */

#ifndef CVC5__LIB__REPLACEMENTS_H
#define CVC5__LIB__REPLACEMENTS_H

#if (defined(__BUILDING_CVC5LIB) || defined(__BUILDING_CVC5LIB_UNIT_TEST)) \
    && !defined(__BUILDING_STATISTICS_FOR_EXPORT)
#include "cvc5_private.h"
#else
#if defined(__BUILDING_CVC5PARSERLIB) \
    || defined(__BUILDING_CVC5PARSERLIB_UNIT_TEST)
#include "cvc5parser_private.h"
#  else
#if defined(__BUILDING_CVC5DRIVER) || defined(__BUILDING_CVC5_SYSTEM_TEST) \
    || defined(__BUILDING_STATISTICS_FOR_EXPORT)
#include "base/cvc5config.h"
#    else
#      error Must be building libcvc5 or libcvc5parser to use replacement functions.  This is because replacement function headers should never be publicly-depended upon, as they should not be installed on user machines with 'make install'.
#    endif
#  endif
#endif

#endif /* CVC5__LIB__REPLACEMENTS_H */
