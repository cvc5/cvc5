/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple stateless conversion to s-expressions.
 */

#include "util/sexpr.h"

#include <iostream>

#include "util/integer.h"
#include "util/rational.h"
#include "util/statistics_value.h"

namespace cvc5 {

void toSExpr(std::ostream& out, const std::string& s)
{
  if (s == "true" || s == "false")
  {
    out << s;
    return;
  }
  try
  {
    Integer tmp(s);
    out << s;
    return;
  }
  catch (std::invalid_argument&)
  {
  }
  try
  {
    Rational tmp(s);
    out << s;
    return;
  }
  catch (std::invalid_argument&)
  {
  }
  out << "\"" << s << "\"";
}
void toSExpr(std::ostream& out, const std::unique_ptr<StatisticBaseValue>& sbv)
{
  out << *sbv;
}

}  // namespace cvc5
