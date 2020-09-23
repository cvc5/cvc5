/*********************                                                        */
/*! \file ostream_util.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for using ostreams.
 **
 ** Utilities for using ostreams.
 **/
#include "util/ostream_util.h"

namespace CVC4 {

StreamFormatScope::StreamFormatScope(std::ostream& out)
    : d_out(out), d_format_flags(out.flags()), d_precision(out.precision())
{
}

StreamFormatScope::~StreamFormatScope()
{
  d_out.precision(d_precision);
  d_out.flags(d_format_flags);
}

}  // namespace CVC4
