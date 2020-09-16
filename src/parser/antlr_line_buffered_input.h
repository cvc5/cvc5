/*********************                                                        */
/*! \file antlr_line_buffered_input.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A custom ANTLR input stream that reads from the input stream lazily
 **
 ** By default, ANTLR expects the whole input to be in a single, consecutive
 ** buffer. When doing incremental solving and the input is coming from the
 ** standard input, this is problematic because CVC4 might receive new input
 ** based on the result of solving the existing input.
 **
 ** This file overwrites the _LA and the consume functions of the input streamto
 ** achieve that and stores the lines received so far in a LineBuffer.
 **/

#include "cvc4parser_private.h"

#ifndef CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H
#define CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H

#include <antlr3.h>
#include <istream>

#include "parser/line_buffer.h"

namespace CVC4 {
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

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H */
