/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The LineBuffer class stores lines from an input stream
 *
 * Each line is guaranteed to be consecutive in memory. The content in
 * the line buffer can be addressed using line number and the position
 * within the line.
 */

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__LINE_BUFFER_H
#define CVC5__PARSER__LINE_BUFFER_H

#include <cstdlib>
#include <istream>
#include <vector>

namespace cvc5 {
namespace parser {

class LineBuffer {
 public:
  static const uint8_t NewLineChar = '\n';

  LineBuffer(std::istream* stream);
  ~LineBuffer();

  /**
    * Gets a pointer to a char at a specific line and position within that
    * line.
    */
  uint8_t* getPtr(size_t line, size_t pos_in_line);

  /**
    * Gets a pointer to a char at an offset relative to a  specific line and
    * position within that line.
    */
  uint8_t* getPtrWithOffset(size_t line, size_t pos_in_line, size_t offset);

  /**
    * Tests whether a given pointer points to a location before a given
    * line and position within that line.
    */
  bool isPtrBefore(uint8_t* ptr, size_t line, size_t pos_in_line);

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
  std::vector<uint8_t*> d_lines;
  // Each element in this vector corresponds to the length of a line from the
  // input stream.
  std::vector<size_t> d_sizes;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__LINE_BUFFER_H */
