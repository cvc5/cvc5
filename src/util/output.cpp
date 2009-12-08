/*********************                                           -*- C++ -*-  */
/** output.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Output utility classes and functions.
 **/

#include "cvc4_config.h"

#include <iostream>
#include "util/output.h"

namespace CVC4 {

null_streambuf null_sb;
std::ostream null_os(&null_sb);

DebugC   Debug  (&std::cout);
WarningC Warning(&std::cerr);
NoticeC  Notice (&std::cout);
ChatC    Chat   (&std::cout);
TraceC   Trace  (&std::cout);

}/* CVC4 namespace */
