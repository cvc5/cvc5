/******************************************
Copyright (c) 2017, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "src/GitSHA1.h"

const char* CMSat::get_version_sha1()
{
    static const char myversion_sha1[] = "43e3983647365e36ec616b4ee92a223537bf4616";
    return myversion_sha1;
}

const char* CMSat::get_version_tag()
{
    static const char myversion_tag[] = "5.6.3";
    return myversion_tag;
}

const char* CMSat::get_compilation_env()
{
    static const char compilation_env[] =
    "CMAKE_CXX_COMPILER = /usr/bin/c++ | "
    "CMAKE_CXX_FLAGS =  -mtune=native -Wall -Wextra -Wunused -Wsign-compare -fno-omit-frame-pointer -Wtype-limits -Wuninitialized -Wno-deprecated -Wstrict-aliasing -Wpointer-arith -Wpointer-arith -Wformat-nonliteral -Winit-self -Wparentheses -Wunreachable-code -ggdb3 -Wlogical-op -Wrestrict -Wnull-dereference -Wdouble-promotion -Wshadow -Wformat=2 -pedantic | "
    "COMPILE_DEFINES =  | "
    "STATICCOMPILE = ON | "
    "ONLY_SIMPLE = ON | "
    "Boost_FOUND = 0 | "
    "STATS = OFF | "
    "SQLITE3_FOUND =  | "
    "ZLIB_FOUND = FALSE | "
    "VALGRIND_FOUND = TRUE | "
    "ENABLE_TESTING = OFF | "
    "M4RI_FOUND =  | "
    "SLOW_DEBUG = OFF | "
    "ENABLE_ASSERTIONS = ON | "
    "PYTHON_EXECUTABLE = /usr/bin/python2.7 | "
    "PYTHON_LIBRARY = /usr/lib/x86_64-linux-gnu/libpython2.7.a | "
    "PYTHON_INCLUDE_DIRS = /usr/include/python2.7 | "
    "MY_TARGETS =  | "
    "LARGEMEM = OFF | "
    "LIMITMEM = OFF | "
    "compilation date time = " __DATE__ " " __TIME__
    ""
    ;
    return compilation_env;
}
