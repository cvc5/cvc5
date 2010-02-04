/*********************                                           -*- C++ -*-  */
/** output.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

/* Definitions of the declared globals from output.h... */

null_streambuf null_sb;
std::ostream null_os(&null_sb);

DebugC   Debug  (&std::cout);
WarningC Warning(&std::cerr);
MessageC Message(&std::cout);
NoticeC  Notice (&std::cout);
ChatC    Chat   (&std::cout);
TraceC   Trace  (&std::cout);

}/* CVC4 namespace */
