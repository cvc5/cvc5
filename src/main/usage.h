/*********************                                                        */
/** usage.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The "usage" string for the CVC4 driver binary.
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
   --lang | -L     force input language (default is `auto'; see --lang help)\n\
   --version | -V  identify this CVC4 binary\n\
   --help | -h     this command line reference\n\
   --verbose | -v  increase verbosity (repeatable)\n\
   --quiet | -q    decrease verbosity (repeatable)\n\
   --trace | -t    tracing for something (e.g. --trace pushpop)\n\
   --debug | -d    debugging for something (e.g. --debug arith), implies -t\n\
   --smtcomp       competition mode (very quiet)\n\
   --stats         give statistics on exit\n\
   --segv-nospin   (debug builds only) don't spin on segfault waiting for gdb\n\
   --parse-only    exit after parsing input\n\
   --no-checking   disable semantic checks in the parser\n\
   --mmap          memory map file input\n\
   --show-config   show CVC4 static configuration\n\
";

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MAIN__USAGE_H */
