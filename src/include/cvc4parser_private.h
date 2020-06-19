/*********************                                                        */
/*! \file cvc4parser_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#  error A private CVC4 parser header was included when not building the parser library or private unit test code.
#endif /* ! (__BUILDING_CVC4PARSERLIB || __BUILDING_CVC4PARSERLIB_UNIT_TEST) */

#include "cvc4parser_public.h"
// It would be nice to #include "cvc4autoconfig.h" here, but there are conflicts
// with antlr3's autoheader stuff, which they export :(
//
// #include "cvc4autoconfig.h"

#endif /* __CVC4PARSER_PRIVATE_H */
