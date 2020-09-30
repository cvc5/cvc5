/*********************                                                        */
/*! \file top_level_substitutions.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Top-level substitutions
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__TOP_LEVEL_SUBSTITUTIONS_H
#define CVC4__PREPROCESSING__TOP_LEVEL_SUBSTITUTIONS_H

#include "context/context.h"
#include "expr/proof_generator.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace preprocessing {

/**
 * Stores a substitution corresponding to a set of equalities that have been
 * inferred from the input at the top level, e.g. the substitution holds
 * globally.
 */
class TopLevelSubstitutions
{
 public:
  TopLevelSubstitutions(context::UserContext * u);
  /** Gets a reference to the top-level substitution map */
  theory::SubstitutionMap& get();
 private:
  /* The top level substitutions */
  theory::SubstitutionMap d_subs;
};

}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__TOP_LEVEL_SUBSTITUTIONS_H */
