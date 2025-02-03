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
 * Implementations of utility methods.
 */

#include "utils.h"

#include <stdio.h>
#include <stdlib.h>

/**
 * Get the string version of define-fun command.
 * @param f       The function to print.
 * @param nparams The number of function parameters.
 * @param params  The function parameters.
 * @param body    The function body.
 * @return A string version of define-fun.
 */
void print_define_fun(const Cvc5Term f,
                      size_t nparams,
                      const Cvc5Term params[],
                      const Cvc5Term body)
{
  Cvc5Sort sort = cvc5_term_get_sort(f);
  if (cvc5_sort_is_fun(sort))
  {
    sort = cvc5_sort_fun_get_codomain(sort);
  }
  printf("(define-fun %s (", cvc5_term_to_string(f));
  for (size_t i = 0; i < nparams; i++)
  {
    printf("%s", i > 0 ? " " : "");
    printf("(%s %s)",
           cvc5_term_to_string(params[i]),
           cvc5_sort_to_string(cvc5_term_get_sort(params[i])));
  }
  printf(") %s %s)", cvc5_sort_to_string(sort), cvc5_term_to_string(body));
}

void print_synth_solutions(size_t nterms,
                           const Cvc5Term terms[],
                           const Cvc5Term sols[])
{
  printf("(\n");
  for (size_t i = 0; i < nterms; i++)
  {
    size_t nparams = 0;
    Cvc5Term* params = NULL;
    Cvc5Term body = sols[i];
    if (cvc5_term_get_kind(sols[i]) == CVC5_KIND_LAMBDA)
    {
      Cvc5Term psols = cvc5_term_get_child(sols[i], 0);
      nparams = cvc5_term_get_num_children(psols);
      params = (Cvc5Term*)malloc(nparams * sizeof(Cvc5Term));
      for (size_t k = 0; k < nparams; k++)
      {
        params[k] = cvc5_term_get_child(psols, k);
      }
      body = cvc5_term_get_child(sols[i], 1);
    }
    printf("  ");
    print_define_fun(terms[i], nterms, params, body);
    if (params)
    {
      free(params);
    }
    printf("\n");
  }
  printf(")\n");
}
