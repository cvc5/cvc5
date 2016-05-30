/*********************                                                        */
/*! \file antlr_line_buffered_input.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

// These headers should be the first two included.
// See the documentation in "parser/antlr_undefines.h" for more details.
#include <antlr3.h>
#include "parser/antlr_undefines.h"

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H
#define __CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H

#include <istream>

namespace CVC4 {
namespace parser {

typedef struct ANTLR3_LINE_BUFFERED_INPUT_STREAM {
  ANTLR3_INPUT_STREAM antlr;
  std::istream* in;
} *pANTLR3_LINE_BUFFERED_INPUT_STREAM;

pANTLR3_INPUT_STREAM
antlr3LineBufferedStreamNew(std::istream& in, ANTLR3_UINT32 encoding, pANTLR3_UINT8 name);

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H */
