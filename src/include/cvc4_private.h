/*********************                                                        */
/*! \file cvc4_private.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief #-inclusion of this file marks a header as private and generates a
 ** warning when the file is included improperly
 **
 ** #-inclusion of this file marks a header as private and generates a
 ** warning when the file is included improperly.
 **/

#ifndef __CVC4_PRIVATE_H
#define __CVC4_PRIVATE_H

#if ! (defined(__BUILDING_CVC4LIB) || defined(__BUILDING_CVC4LIB_UNIT_TEST))
#  warning A private CVC4 header was included when not building the library or private unit test code.
#endif /* ! (__BUILDING_CVC4LIB || __BUILDING_CVC4LIB_UNIT_TEST) */

#ifdef __BUILDING_STATISTICS_FOR_EXPORT
#  warning A private CVC4 header was included when building a library for export.
#endif /* __BUILDING_STATISTICS_FOR_EXPORT */

#include "cvc4_public.h"
#include "cvc4autoconfig.h"

#endif /* __CVC4_PRIVATE_H */
