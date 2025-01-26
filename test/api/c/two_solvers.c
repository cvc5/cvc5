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
 * A simple test of multiple SmtEngines.
 */

#include <cvc5/c/cvc5.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* solver1 = cvc5_new(tm);
  Cvc5* solver2 = cvc5_new(tm);
  Cvc5Term assumptions[1] = {cvc5_mk_false(tm)};
  Cvc5Result res1 = cvc5_check_sat_assuming(solver1, 1, assumptions);
  Cvc5Result res2 = cvc5_check_sat_assuming(solver2, 1, assumptions);
  int res = cvc5_result_is_unsat(res1) && cvc5_result_is_unsat(res2) ? 0 : 1;
  cvc5_delete(solver1);
  cvc5_delete(solver2);
  cvc5_term_manager_delete(tm);
  return res;
}
