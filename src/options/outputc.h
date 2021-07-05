#include "cvc5_private_library.h"

#ifndef CVC5__OPTIONS__OUTPUTC_H
#define CVC5__OPTIONS__OUTPUTC_H

#include <iostream>

#include "cvc5_export.h"
#include "base/output.h"
#include "options/base_options.h"

namespace cvc5 {

class OutputC
{
 public:
  explicit OutputC(std::ostream* os) : d_os(os) {}

  Cvc5ostream operator()(const options::OutputTag tag) const;

  bool isOn(const options::OutputTag tag) const;

 private:
  std::ostream* d_os;

}; /* class OutputC */

extern OutputC OutputChannel CVC5_EXPORT;

#ifdef CVC5_MUZZLE
#define Output ::cvc5::__cvc5_true() ? ::cvc5::nullStream : ::cvc5::OutputChannel
#else /* CVC5_MUZZLE */
#define Output ::cvc5::OutputChannel
#endif /* CVC5_MUZZLE */

}

#endif /* CVC5__OPTIONS__OUTPUTC_H */
