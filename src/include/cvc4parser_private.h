/*********************                                                        */
/*! \file cvc4parser_private.h
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
 ** warning when the file is included improperly.
 **
 ** #-inclusion of this file marks a header as private and generates a
 ** warning when the file is included improperly.
 **/

#ifndef __CVC4PARSER_PRIVATE_H
#define __CVC4PARSER_PRIVATE_H

#if ! (defined(__BUILDING_CVC4PARSERLIB) || defined(__BUILDING_CVC4PARSERLIB_UNIT_TEST))
#  warning A private CVC4 parser header was included when not building the parser library or private unit test code.
#endif /* ! (__BUILDING_CVC4PARSERLIB || __BUILDING_CVC4PARSERLIB_UNIT_TEST) */

#include "cvc4parser_public.h"
// It would be nice to #include this here, but there are conflicts with
// antlr3's autoheader stuff, which they export :(
//
// #include "cvc4autoconfig.h"

#endif /* __CVC4PARSER_PRIVATE_H */
