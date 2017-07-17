#include "util/index.h"

#include <cstddef>
#include <limits>

namespace CVC4 {

static_assert(sizeof(Index) <= sizeof(size_t),
              "Index cannot be larger than size_t");
static_assert(!std::numeric_limits<Index>::is_signed,
              "Index must be unsigned");

/* Discussion: Why is Index a uint32_t instead of size_t (or uint_fast32_t)?
 *
 * size_t is a more appropriate choice than uint32_t as the choice is dictated
 * by uniqueness in arrays and vectors. These correspond to size_t. However, the
 * using size_t with a sizeof == 8 on 64 bit platforms is noticeably slower.
 * (Limited testing suggests a ~1/16 of running time.) Interestingly,
 * uint_fast32_t also has a sizeof == 8 on x86_64.
 */
}/* CVC4 namespace */
