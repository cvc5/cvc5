/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for using ostreams.
 */
#include "util/ostream_util.h"

#include <ostream>

namespace cvc5::internal {

StreamFormatScope::StreamFormatScope(std::ostream& out)
    : d_out(out), d_format_flags(out.flags()), d_precision(out.precision())
{
}

StreamFormatScope::~StreamFormatScope()
{
  d_out.precision(d_precision);
  d_out.flags(d_format_flags);
}

}  // namespace cvc5::internal
