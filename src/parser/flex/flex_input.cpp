/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of SMT2 tokens.
 */

#include "parser/flex/flex_input.h"

#include <fstream>

namespace cvc5 {
namespace parser {

/** File input class */
class FlexFileInput : public FlexInput
{
 public:
  FlexFileInput(const std::string& filename) : FlexInput()
  {
    d_fs.open(filename, std::fstream::in);
    if (!d_fs.is_open())
    {
      std::stringstream ss;
      ss << "Could not open file " << filename << " for reading.";
      FlexInput::reportError(ss.str());
    }
  }
  std::istream& getStream() override { return d_fs; }

 private:
  /** File stream */
  std::ifstream d_fs;
};

class FlexStreamInput : public FlexInput
{
 public:
  FlexStreamInput(std::istream& input) : FlexInput(), d_input(input) {}
  std::istream& getStream() override { return d_input; }

 private:
  /** Reference to stream */
  std::istream& d_input;
};

FlexInput::FlexInput() {}

std::unique_ptr<FlexInput> FlexInput::mkFileInput(const std::string& filename)
{
  return std::unique_ptr<FlexInput>(new FlexFileInput(filename));
}

std::unique_ptr<FlexInput> FlexInput::mkStreamInput(std::istream& input)
{
  return std::unique_ptr<FlexInput>(new FlexStreamInput(input));
}

std::unique_ptr<FlexInput> FlexInput::mkStringInput(const std::string& input)
{
  // TODO
  return nullptr;
}

void FlexInput::reportError(const std::string&)
{
  // TODO
}

}  // namespace parser
}  // namespace cvc5
