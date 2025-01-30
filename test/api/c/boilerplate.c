/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple start-up/tear-down test for cvc5.
 *
 * This simple test just makes sure that the public interface is
 * minimally functional.  It is useful as a template to use for other
 * system tests.
 */

#include <cvc5/c/cvc5.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* solver = cvc5_new(tm);

  Cvc5Term assumptions[1] = {cvc5_mk_false(tm)};
  Cvc5Result r = cvc5_check_sat_assuming(solver, 1, assumptions);
  int res = cvc5_result_is_unsat(r) ? 0: 1;
  cvc5_delete(solver);
  cvc5_term_manager_delete(tm);
  return res;
}

