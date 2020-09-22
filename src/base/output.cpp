/*********************                                                        */
/*! \file output.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Output utility classes and functions
 **
 ** Output utility classes and functions.
 **/

#include "base/output.h"

#include <iostream>

using namespace std;

namespace CVC4 {

/* Definitions of the declared globals from output.h... */

null_streambuf null_sb;
ostream null_os(&null_sb);

NullC nullCvc4Stream CVC4_PUBLIC;

const std::string CVC4ostream::s_tab = "  ";
const int CVC4ostream::s_indentIosIndex = ios_base::xalloc();

DebugC DebugChannel CVC4_PUBLIC (&cout);
WarningC WarningChannel CVC4_PUBLIC (&cerr);
MessageC MessageChannel CVC4_PUBLIC (&cout);
NoticeC NoticeChannel CVC4_PUBLIC (&null_os);
ChatC ChatChannel CVC4_PUBLIC (&null_os);
TraceC TraceChannel CVC4_PUBLIC (&cout);
std::ostream DumpOutC::dump_cout(cout.rdbuf());// copy cout stream buffer
DumpOutC DumpOutChannel CVC4_PUBLIC (&DumpOutC::dump_cout);

}/* CVC4 namespace */
