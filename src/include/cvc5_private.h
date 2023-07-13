/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner
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

#ifndef CVC5_PRIVATE_H
#define CVC5_PRIVATE_H

#if !(defined(__BUILDING_CVC5LIB) || defined(__BUILDING_CVC5LIB_UNIT_TEST))
#  error A private cvc5 header was included when not building the library or private unit test code.
#endif

#include "base/cvc5config.h"
#include "cvc5_public.h"

#endif /* CVC5_PRIVATE_H */
