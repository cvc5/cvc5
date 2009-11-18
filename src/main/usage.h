#ifndef __CVC4_USAGE_H
#define __CVC4_USAGE_H

namespace CVC4 {
namespace Main {

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

}/* CVC4::Main namespace */
}/* CVC4 namespace */

#endif /* __CVC4_USAGE_H */
