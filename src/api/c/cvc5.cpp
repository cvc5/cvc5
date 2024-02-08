/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 C API.
 */

#include <cvc5/c/cvc5.h>
#include <cvc5/cvc5.h>

#include <iostream>

#include "api/c/cvc5_checks.h"

/* Cvc5Kind ----------------------------------------------------------------- */

size_t cvc5_kind_hash(Cvc5Kind kind)
{
  return std::hash<cvc5::Kind>{}(static_cast<cvc5::Kind>(kind));
}

const char* cvc5_kind_to_string(Cvc5Kind kind)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_KIND(kind);
  str = "CVC5_KIND_" + kindToString(static_cast<cvc5::Kind>(kind));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}

/* Cvc5SortKind ------------------------------------------------------------- */

size_t cvc5_sort_kind_hash(Cvc5SortKind kind)
{
  return std::hash<cvc5::SortKind>{}(static_cast<cvc5::SortKind>(kind));
}

const char* cvc5_sort_kind_to_string(Cvc5SortKind kind)
{
  static thread_local std::string str;
  CVC5_CAPI_TRY_CATCH_BEGIN;
  CVC5_CAPI_CHECK_SORT_KIND(kind);
  str = "CVC5_SORT_KIND_" + sortKindToString(static_cast<cvc5::SortKind>(kind));
  CVC5_CAPI_TRY_CATCH_END;
  return str.c_str();
}
