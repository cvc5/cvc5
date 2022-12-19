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
 * Flex input class.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__FLEX_INPUT_H
#define CVC5__PARSER__FLEX_INPUT_H

#include <memory>
#include <sstream>
#include <string>

namespace cvc5 {
namespace parser {

/**
 * Wrapper to setup the necessary information for constructing a flex Lexer.
 *
 * Currently this is std::istream& obtainable via getStream.
 */
class FlexInput
{
 public:
  FlexInput();
  virtual ~FlexInput() {}
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  static std::unique_ptr<FlexInput> mkFileInput(const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  static std::unique_ptr<FlexInput> mkStreamInput(std::istream& input);

  /** Set the input for the given string
   *
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static std::unique_ptr<FlexInput> mkStringInput(const std::string& input);
  /** Get the stream to pass to the flex lexer. */
  virtual std::istream& getStream() = 0;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
