/*********************                                                        */
/*! \file memory_mapped_input_buffer.h
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief ANTLR input buffer from a memory-mapped file.
 **
 ** ANTLR input buffer from a memory-mapped file.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H
#define __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H

#include <antlr3input.h>
#include <string>

namespace CVC4 {
namespace parser {

#ifdef __cplusplus
extern "C" {
#endif

pANTLR3_INPUT_STREAM
MemoryMappedInputBufferNew(const std::string& filename);

#ifdef __cplusplus
}/* extern "C" */
#endif

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__MEMORY_MAPPED_INPUT_BUFFER_H */
