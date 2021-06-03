/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A custom ANTLR input stream that reads from the input stream lazily
 *
 * By default, ANTLR expects the whole input to be in a single, consecutive
 * buffer. When doing incremental solving and the input is coming from the
 * standard input, this is problematic because cvc5 might receive new input
 * based on the result of solving the existing input.
 *
 * This file overwrites the _LA and the consume functions of the input streamto
 * achieve that and stores the lines received so far in a LineBuffer.
 */

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__ANTLR_LINE_BUFFERED_INPUT_H
#define CVC5__PARSER__ANTLR_LINE_BUFFERED_INPUT_H

#include <antlr3.h>
#include <istream>

#include "parser/line_buffer.h"

namespace cvc5 {
namespace parser {

typedef struct ANTLR3_LINE_BUFFERED_INPUT_STREAM {
  ANTLR3_INPUT_STREAM antlr;
  std::istream* in;
  LineBuffer* line_buffer;
} *pANTLR3_LINE_BUFFERED_INPUT_STREAM;

pANTLR3_INPUT_STREAM antlr3LineBufferedStreamNew(std::istream& in,
                                                 ANTLR3_UINT32 encoding,
                                                 pANTLR3_UINT8 name,
                                                 LineBuffer* line_buffer);

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__ANTLR_LINE_BUFFERED_INPUT_H */
