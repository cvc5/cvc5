/*********************                                                        */
/*! \file top_level_substitutions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Top-level substitutions
 **/

#include "preprocessing/top_level_substitutions.h"

#include "expr/node_algorithm.h"

namespace CVC4 {
namespace preprocessing {

TopLevelSubstitutions::TopLevelSubstitutions(
    context::UserContext * u)
    :  d_subs(u)
{
}

theory::SubstitutionMap& TopLevelSubstitutions::get()
{
  return d_subs;
}

}  // namespace preprocessing
}  // namespace CVC4
