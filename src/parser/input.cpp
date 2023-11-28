/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 *  input class.
 */

#include "parser/input.h"

#include <fstream>

#include "parser/parser_exception.h"

namespace cvc5 {
namespace parser {

/** File input class */
class FileInput : public Input
{
 public:
  FileInput(const std::string& filename) : Input()
  {
    d_fs.open(filename, std::fstream::in);
    if (!d_fs.is_open())
    {
      std::stringstream ss;
      ss << "Couldn't open file: " << filename;
      throw InputStreamException(ss.str());
    }
  }
  std::istream* getStream() override { return &d_fs; }

 private:
  /** File stream */
  std::ifstream d_fs;
};

/** Stream reference input class */
class StreamInput : public Input
{
 public:
  StreamInput(std::istream& input) : Input(), d_input(input) {}
  std::istream* getStream() override { return &d_input; }
  bool isInteractive() const override { return true; }

 private:
  /** Reference to stream */
  std::istream& d_input;
};

/** String input class, which buffers to a std::stringstream */
class StringInput : public Input
{
 public:
  StringInput(const std::string& input) : Input() { d_input << input; }
  std::istream* getStream() override { return &d_input; }

 private:
  /** Reference to stream */
  std::stringstream d_input;
};

Input::Input() {}

std::unique_ptr<Input> Input::mkFileInput(const std::string& filename)
{
  return std::unique_ptr<Input>(new FileInput(filename));
}

std::unique_ptr<Input> Input::mkStreamInput(std::istream& input)
{
  return std::unique_ptr<Input>(new StreamInput(input));
}

std::unique_ptr<Input> Input::mkStringInput(const std::string& input)
{
  return std::unique_ptr<Input>(new StringInput(input));
}
bool Input::isInteractive() const { return false; }

}  // namespace parser
}  // namespace cvc5
