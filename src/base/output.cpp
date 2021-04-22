/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Output utility classes and functions.
 */

#include "base/output.h"

#include <iostream>

using namespace std;

namespace cvc5 {

/* Definitions of the declared globals from output.h... */

null_streambuf null_sb;
ostream null_os(&null_sb);

NullC nullStream;

const std::string Cvc5ostream::s_tab = "  ";
const int Cvc5ostream::s_indentIosIndex = ios_base::xalloc();

DebugC DebugChannel(&cout);
WarningC WarningChannel(&cerr);
MessageC MessageChannel(&cout);
NoticeC NoticeChannel(&null_os);
ChatC ChatChannel(&null_os);
TraceC TraceChannel(&cout);
std::ostream DumpOutC::dump_cout(cout.rdbuf());// copy cout stream buffer
DumpOutC DumpOutChannel(&DumpOutC::dump_cout);

}  // namespace cvc5
