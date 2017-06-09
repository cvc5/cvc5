/*********************                                                        */
/*! \file line_buffer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The LineBuffer class stores lines from an input stream
 **
 ** Each line is guaranteed to be consecutive in memory. The content in
 ** the line buffer can be addressed using line number and the position
 ** within the line.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__SEGMENTED_BUFFER_H
#define __CVC4__PARSER__SEGMENTED_BUFFER_H

#include <cstdlib>
#include <istream>
#include <vector>

namespace CVC4 {
namespace parser {

class LineBuffer {
 public:
  LineBuffer(std::istream* stream);
  ~LineBuffer();

  /**
    * Gets a pointer to a char at a specific line and position within that
    * line.
    */
  char* getPtr(size_t line, size_t pos_in_line);

  /**
    * Gets a pointer to a char at an offset relative to a  specific line and
    * position within that line.
    */
  char* getPtrWithOffset(size_t line, size_t pos_in_line, size_t offset);

 private:
  /**
    * Reads lines up to a line number from the input if needed (it does
    * nothing for the lines that were already read). Returns false if the end
    * of the input stream has been reached and not all lines could be read.
    */
  bool readToLine(size_t line);

  std::istream* d_stream;
  // Each element in this vector corresponds to a line from the input stream.
  // WARNING: not null-terminated.
  std::vector<char*> d_lines;
  // Each element in this vector corresponds to the length of a line from the
  // input stream.
  std::vector<size_t> d_sizes;
};

}  // namespace parser
}  // namespace CVC4

#endif /* __CVC4__PARSER__SEGMENTED_BUFFER_H */
