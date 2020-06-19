/*********************                                                        */
/*! \file memory_mapped_input_buffer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add file-specific comments here ]].
 **
 ** [[ Add file-specific comments here ]]
 **/

#include <fcntl.h>
#include <stdio.h>
#include <stdint.h>

#include <antlr3input.h>

#ifndef _WIN32

#include <cerrno>
#include <sys/mman.h>
#include <sys/stat.h>

#endif /* _WIN32 */

#include "base/exception.h"
#include "parser/memory_mapped_input_buffer.h"

namespace CVC4 {
namespace parser {

extern "C" {

#ifdef _WIN32

pANTLR3_INPUT_STREAM MemoryMappedInputBufferNew(const std::string& filename) {
  return 0;
}

#else /* ! _WIN32 */

static ANTLR3_UINT32
MemoryMapFile(pANTLR3_INPUT_STREAM input, const std::string& filename);

void
UnmapFile(pANTLR3_INPUT_STREAM input);

pANTLR3_INPUT_STREAM MemoryMappedInputBufferNew(const std::string& filename) {
  // Pointer to the input stream we are going to create
  //
  pANTLR3_INPUT_STREAM input;
  ANTLR3_UINT32 status;

  // Allocate memory for the input stream structure
  //
  input = (pANTLR3_INPUT_STREAM) ANTLR3_CALLOC(1, sizeof(ANTLR3_INPUT_STREAM));

  if(input == NULL) {
    return NULL;
  }

  // Structure was allocated correctly, now we can read the file.
  //
  status = MemoryMapFile(input, filename);

  // Call the common 8 bit ASCII input stream handler
  // Initializer type thingy doobry function.
  //
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  antlr3AsciiSetupStream(input, ANTLR3_CHARSTREAM);
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  antlr38BitSetupStream(input);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */

  // Now we can set up the file name
  //
  input->istream->streamName
      = input->strFactory->newStr(input->strFactory,
                                  (uint8_t*) filename.c_str());
  input->fileName = input->istream->streamName;
  input->free = UnmapFile;

  if(status != ANTLR3_SUCCESS) {
    input->close(input);
    return NULL;
  }

  return input;
}

static ANTLR3_UINT32 MemoryMapFile(pANTLR3_INPUT_STREAM input,
                                   const std::string& filename) {
  errno = 0;
  struct stat st;
  if(stat(filename.c_str(), &st) == -1) {
    return ANTLR3_ERR_NOFILE;
  }

  input->sizeBuf = st.st_size;

  int fd = open(filename.c_str(), O_RDONLY);
  if(fd == -1) {
    return ANTLR3_ERR_NOFILE;
  }

  input->data = mmap(0, input->sizeBuf, PROT_READ, MAP_PRIVATE, fd, 0);
  errno = 0;
  close(fd);
  if(intptr_t(input->data) == -1) {
    return ANTLR3_ERR_NOMEM;
  }

  return ANTLR3_SUCCESS;
}

/* This is a bit shady. antlr3AsciiSetupStream has free and close as aliases.
 * We need to unmap the file somewhere, so we install this function as free and
 * call the default version of close to de-allocate everything else. */
void UnmapFile(pANTLR3_INPUT_STREAM input) {
  munmap((void*) input->data, input->sizeBuf);
  input->close(input);
}

#endif /* _WIN32 */

}/* extern "C" */

}/* CVC4::parser namespace */
}/* CVC4 namespace */
