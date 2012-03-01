/*********************                                                        */
/*! \file antlr_line_buffered_input.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H
#define __CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H

#include <antlr3.h>

namespace CVC4 {
namespace parser {

pANTLR3_INPUT_STREAM
antlr3LineBufferedStreamNew(std::istream& in, ANTLR3_UINT32 encoding, pANTLR3_UINT8 name);

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_LINE_BUFFERED_INPUT_H */
