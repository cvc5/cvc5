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

#include <antlr3input.h>
#include <string>

namespace CVC4 {
namespace parser {

extern "C" {

pANTLR3_INPUT_STREAM
MemoryMappedInputBufferNew(const std::string& filename);

}

}
}


#endif /* __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H */
