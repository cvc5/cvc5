/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inclusion of this file marks a header as private and generates a warning
 * when the file is included improperly.
 */

#ifndef CVC5PARSER_PRIVATE_H
#define CVC5PARSER_PRIVATE_H

#if !(defined(__BUILDING_CVC5PARSERLIB) \
      || defined(__BUILDING_CVC5PARSERLIB_UNIT_TEST))
#  error A private cvc5 parser header was included when not building the parser library or private unit test code.
#endif

#include "cvc5parser_public.h"
// It would be nice to #include "base/cvc5config.h" here, but there are
// conflicts with antlr3's autoheader stuff, which they export :(
//
// #include "base/cvc5config.h"

#endif /* CVC5PARSER_PRIVATE_H */
