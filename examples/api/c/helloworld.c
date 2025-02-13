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
 * A very simple cvc5 example.
 */

#include <cvc5/c/cvc5.h>
#include <stdio.h>

int main()
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  Cvc5Term hello = cvc5_mk_const(tm, cvc5_get_boolean_sort(tm), "Hello World!");
  Cvc5Term assumptions[1] = {hello};
  printf("%s is %s\n",
         cvc5_term_to_string(hello),
         cvc5_result_to_string(cvc5_check_sat_assuming(slv, 1, assumptions)));
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  return 0;
}
