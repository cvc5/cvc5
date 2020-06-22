/*********************                                                        */
/*! \file line_buffer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The LineBuffer class stores lines from an input stream
 **
 ** For each line, the class allocates a separate buffer.
 **/

#include "parser/line_buffer.h"

#include <cassert>
#include <cstring>
#include <iostream>
#include <string>

namespace CVC4 {
namespace parser {

LineBuffer::LineBuffer(std::istream* stream) : d_stream(stream) {}

LineBuffer::~LineBuffer() {
  for (size_t i = 0; i < d_lines.size(); i++) {
    delete[] d_lines[i];
  }
}

uint8_t* LineBuffer::getPtr(size_t line, size_t pos_in_line) {
  if (!readToLine(line)) {
    return NULL;
  }
  assert(pos_in_line < d_sizes[line]);
  return d_lines[line] + pos_in_line;
}

uint8_t* LineBuffer::getPtrWithOffset(size_t line, size_t pos_in_line,
                                   size_t offset) {
  if (!readToLine(line)) {
    return NULL;
  }
  if (pos_in_line + offset >= d_sizes[line]) {
    return getPtrWithOffset(line + 1, 0,
                            offset - (d_sizes[line] - pos_in_line - 1));
  }
  assert(pos_in_line + offset < d_sizes[line]);
  return d_lines[line] + pos_in_line + offset;
}

bool LineBuffer::isPtrBefore(uint8_t* ptr, size_t line, size_t pos_in_line) {
  for (size_t j = 0; j < line; j++)
  {
    // NOTE: std::less is guaranteed to give consistent results when comparing
    // pointers of different arrays (in contrast to built-in comparison
    // operators).
    size_t i = line - j;
    uint8_t* end = d_lines[i] + ((i == line) ? pos_in_line : d_sizes[i]);
    if (std::less<uint8_t*>()(d_lines[i] - 1, ptr) &&
        std::less<uint8_t*>()(ptr, end)) {
      return true;
    }
  }
  return false;
}

bool LineBuffer::readToLine(size_t line_size)
{
  while (line_size >= d_lines.size())
  {
    if (!(*d_stream)) {
      return false;
    }

    std::string line;
    std::getline(*d_stream, line);
    uint8_t* segment = new uint8_t[line.size() + 1];
    std::memcpy(segment, line.c_str(), line.size());
    segment[line.size()] = LineBuffer::NewLineChar;
    d_lines.push_back(segment);
    d_sizes.push_back(line.size() + 1);
  }
  return true;
}

}  // namespace parser
}  // namespace CVC4
