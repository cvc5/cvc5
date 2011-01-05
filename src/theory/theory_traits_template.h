/*
 * theory_traits_template.h
 *
 *  Created on: Dec 23, 2010
 *      Author: dejan
 */

#pragma once

#include "theory/theory.h"

${theory_includes}

namespace CVC4 {

namespace theory {

template <TheoryId theoryId>
struct TheoryTraits;

${theory_traits}

${theory_for_each_macro}

}/* theory namespace */
}/* CVC4 namespace */
