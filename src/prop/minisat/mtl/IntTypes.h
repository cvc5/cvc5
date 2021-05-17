/**************************************************************************************[IntTypes.h]
Copyright (c) 2009-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_IntTypes_h
#define Minisat_IntTypes_h

#ifdef __sun
    // Not sure if there are newer versions that support C99 headers. The
    // needed features are implemented in the headers below though:

#   include <sys/int_types.h>
#   include <sys/int_fmtio.h>
#   include <sys/int_limits.h>

#else

// In contrast to the original MiniSat source code, we are including the
// cstdint/cinttypes/climits headers instead of stdint.h/inttypes.h/limits.h
// here. This ensures that the macros in cinttypes/inttypes.h such as PRIi64
// are actually defined. The C99 standard suggested that those macros are only
// defined for C++ code when __STDC_FORMAT_MACROS is defined. This was never
// adopted by a C++ standard (https://en.cppreference.com/w/cpp/types/integer).
// However, certain versions of mingw-w64 seem to require it with inttypes.h
// but not cinttypes.
#   include <cstdint>
#   include <cinttypes>

#endif

#include <climits>

//=================================================================================================

#endif
