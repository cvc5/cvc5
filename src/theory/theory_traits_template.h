/*********************                                                        */
/*! \file theory_traits_template.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A template for the theory_traits.h header, defining various
 ** (static) aspects of theories
 **
 ** This file is a template for the theory_traits.h header, defining
 ** various (static) aspects of theories, combined with the theory
 ** kinds files to produce the final header.
 **/

#pragma once

#include "cvc4_private.h"
#include "theory/theory.h"

${theory_includes}

namespace CVC4 {
namespace theory {

template <TheoryId theoryId>
struct TheoryTraits;

${theory_traits}

${theory_for_each_macro}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
