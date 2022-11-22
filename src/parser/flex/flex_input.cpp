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

#include "flex/parser/flex_input.h"

namespace cvc5 {
namespace parser {

class FlexFileInput : public FlexInput
{
 public:
  FlexFileInput(const std::string& filename) : FlexInput()
  {
    d_fs.open(filename, std::fstream::in);
    if (!d_fs.is_open())
    {
      // TODO: error
      exit(1);
    }
  }
  std::istream& getStream() override { return d_fs; }

 private:
  /** File stream */
  std::ifstream d_fs;
};

FlexInput::FlexInput() {}

std::unique_ptr<FlexInput> FlexInput::setFileInput(const std::string& filename)
{
  std::unique_ptr<FlexFileInput> finput(filename);
  return finput;
}

std::unique_ptr<FlexInput> FlexInput::setStreamInput(std::istream& input)
{
  // TODO
  return nullptr;
}

std::unique_ptr<FlexInput> FlexInput::setStringInput(const std::string& input)
{
  // TODO
  return nullptr;
}

}  // namespace parser
}  // namespace cvc5
