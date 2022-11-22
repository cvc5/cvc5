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

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__FLEX_INPUT_H
#define CVC5__PARSER__FLEX_INPUT_H

#include <optional>
#include <sstream>
#include <string>

namespace cvc5 {
namespace parser {
  
/**
 */
class FlexInput
{
 public:
  FlexInput();
  virtual ~FlexInput(){}
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  static FlexInput* mkFileInput(const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  static FlexInput* mkStreamInput(std::istream& input);

  /** Set the input for the given string
   *
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static FlexInput* mkStringInput(const std::string& input);
  /** get stream */
  virtual std::istream& getStream() = 0;
private:
  // Used to report errors, with the current source location attached.
  static void report_error(const std::string&);
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
