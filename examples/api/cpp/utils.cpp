/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementations of utility methods.
 */

#include "utils.h"

#include <iostream>

/**
 * Get the string version of define-fun command.
 * @param f the function to print
 * @param params the function parameters
 * @param body the function body
 * @return a string version of define-fun
 */
std::string defineFunToString(const cvc5::api::Term& f,
                              const std::vector<cvc5::api::Term> params,
                              const cvc5::api::Term body)
{

  cvc5::api::Sort sort = f.getSort();
  if (sort.isFunction())
  {
    sort = sort.getFunctionCodomainSort();
  }
  std::stringstream ss;
  ss << "(define-fun " << f << " (";
  for (size_t i = 0, n = params.size(); i < n; ++i)
  {
    if (i > 0)
    {
      ss << ' ';
    }
    ss << '(' << params[i] << ' ' << params[i].getSort() << ')';
  }
  ss << ") " << sort << ' ' << body << ')';
  return ss.str();
}

void printSynthSolutions(const std::vector<cvc5::api::Term>& terms,
                         const std::vector<cvc5::api::Term>& sols)
{
  std::cout << '(' << std::endl;

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    std::vector<cvc5::api::Term> params;
    cvc5::api::Term body;
    if (sols[i].getKind() == cvc5::api::LAMBDA)
    {
      params.insert(params.end(), sols[i][0].begin(), sols[i][0].end());
      body = sols[i][1];
    }
    std::cout << "  " << defineFunToString(terms[i], params, body)
              << std::endl;
  }
  std::cout << ')' << std::endl;
}
