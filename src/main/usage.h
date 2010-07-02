/*********************                                                        */
/*! \file usage.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The "usage" string for the CVC4 driver binary.
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
   --lang | -L            force input language (default is `auto'; see --lang help)\n\
   --version | -V         identify this CVC4 binary\n\
   --help | -h            this command line reference\n\
   --parse-only           exit after parsing input\n\
   --mmap                 memory map file input\n\
   --show-config          show CVC4 static configuration\n\
   --segv-nospin          don't spin on segfault waiting for gdb\n\
   --no-checking          disable semantic checks in the parser\n\
   --strict-parsing       fail on inputs that are not strictly conformant (SMT2 only)\n\
   --verbose | -v         increase verbosity (repeatable)\n\
   --quiet | -q           decrease verbosity (repeatable)\n\
   --trace | -t           tracing for something (e.g. --trace pushpop)\n\
   --debug | -d           debugging for something (e.g. --debug arith), implies -t\n\
   --stats                give statistics on exit\n\
   --default-expr-depth=N print exprs to depth N (0 == default, -1 == no limit)\n\
   --print-expr-types     print types with variables when printing exprs\n"
;

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif /* __CVC4__MAIN__USAGE_H */
