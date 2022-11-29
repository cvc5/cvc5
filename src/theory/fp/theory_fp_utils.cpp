#include "theory/fp/theory_fp_utils.h"

namespace cvc5::internal {
namespace theory {
namespace fp {
namespace utils {

Integer getCardinality(const TypeNode& type)
{
  Assert(type.getKind() == kind::FLOATINGPOINT_TYPE);

  FloatingPointSize fps = type.getConst<FloatingPointSize>();

  /*
   * 1                    NaN
   * 2*1                  Infinities
   * 2*1                  Zeros
   * 2*2^(s-1)            Subnormal
   * 2*((2^e)-2)*2^(s-1)  Normal
   *
   *  = 1 + 2*2 + 2*((2^e)-1)*2^(s-1)
   *  =       5 + ((2^e)-1)*2^s
   */

  return Integer(5)
         + Integer(2).pow(fps.significandWidth())
               * (Integer(2).pow(fps.exponentWidth()) - Integer(1));
}

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
