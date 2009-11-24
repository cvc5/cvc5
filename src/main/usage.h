/*********************                                           -*- C++ -*-  */
/** usage.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#ifndef __CVC4__MAIN__USAGE_H
#define __CVC4__MAIN__USAGE_H

namespace CVC4 {
namespace main {

// no more % chars in here without being escaped; it's used as a
// printf() format string
const char usage[] = "\
usage: %s [options] [input-file]\n\
\n\
Without an input file, or with `-', CVC4 reads from standard input.\n\
\n\
CVC4 options:\n\
   --lang | -L     set input language (--lang help gives a list;\n\
                                       `auto' is default)\n\
   --version | -V  identify this CVC4 binary\n\
   --help | -h     this command line reference\n\
   --verbose | -v  increase verbosity (repeatable)\n\
   --quiet | -q    decrease verbosity (repeatable)\n\
   --debug | -d    debugging for something (e.g. --debug arith)\n\
   --smtcomp       competition mode (very quiet)\n\
   --stats         give statistics on exit\n\
";

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MAIN__USAGE_H */
