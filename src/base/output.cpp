/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Output utility classes and functions.
 */

#include "base/output.h"

#include <iostream>

namespace cvc5::internal {

/* Definitions of the declared globals from output.h... */

null_streambuf null_sb;
std::ostream null_os(&null_sb);

NullC nullStream;

const std::string Cvc5ostream::s_tab = "  ";
const int Cvc5ostream::s_indentIosIndex = std::ios_base::xalloc();

WarningC WarningChannel(&std::cerr);
TraceC TraceChannel(&std::cout);

}  // namespace cvc5::internal
