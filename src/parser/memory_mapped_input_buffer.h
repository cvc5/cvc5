/*********************                                                        */
/** memory_mapped_input_buffer.cpp
 ** Original author: cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** ANTLR input buffer from a memory-mapped file.
 **/

#ifndef __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H
#define __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H

#include <cstdio>
#include <cerrno>

#include <fcntl.h>
#include <stdint.h>
#include <string.h>

#include <sys/mman.h>
#include <sys/stat.h>

#include <antlr/InputBuffer.hpp>

#include "util/Assert.h"
#include "util/exception.h"

namespace CVC4 {
namespace parser {

class MemoryMappedInputBuffer : public antlr::InputBuffer {

public:
  MemoryMappedInputBuffer(const std::string& filename) {
    struct stat st;
    if( stat(filename.c_str(), &st) == -1 ) {
      char buf[80];
      const char* errMsg = strerror_r(errno, buf, sizeof(buf));
      throw Exception("unable to stat() file `" + filename + "': " + errMsg);
    }
    d_size = st.st_size;

    int fd = open(filename.c_str(), O_RDONLY);
    if( fd == -1 ) {
      char buf[80];
      const char* errMsg = strerror_r(errno, buf, sizeof(buf));
      throw Exception("unable to fopen() file `" + filename + "': " + errMsg);
    }

    d_start = static_cast< const char * >(
        mmap( 0, d_size, PROT_READ, MAP_FILE | MAP_PRIVATE, fd, 0 ) );
    if( intptr_t( d_start ) == -1 ) {
      char buf[80];
      const char* errMsg = strerror_r(errno, buf, sizeof(buf));
      throw Exception("unable to mmap() file `" + filename + "': " + errMsg);
    }
    d_cur = d_start;
    d_end = d_start + d_size;
  }

  ~MemoryMappedInputBuffer() {
    munmap((void*) d_start, d_size);
  }

  inline int getChar() {
    Assert( d_cur >= d_start && d_cur <= d_end );
    return d_cur == d_end ? EOF : *d_cur++;
  }

private:
  unsigned long int d_size;
  const char *d_start, *d_end, *d_cur;
};

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H */
