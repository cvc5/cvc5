/******************************************************************************
 * Top contributors (to current version):
 *   Christopher L. Conway, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A super-class for input language parsers
 */

// This must be included first.
#include "parser/antlr_input.h"

#include "parser/input.h"

#include "base/output.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"


using namespace std;
using namespace cvc5;
using namespace cvc5::parser;

namespace cvc5 {
namespace parser {

InputStreamException::InputStreamException(const std::string& msg) :
  Exception(msg) {
}

const std::string InputStream::getName() const {
  return d_name;
}

Input::Input(InputStream& inputStream) :
    d_inputStream( &inputStream ) {
}

Input::~Input() {
  delete d_inputStream;
}

InputStream *Input::getInputStream() {
  return d_inputStream;
}

Input* Input::newFileInput(const std::string& lang,
                           const std::string& filename,
                           bool useMmap)
{
  AntlrInputStream *inputStream = 
    AntlrInputStream::newFileInputStream(filename, useMmap);
  return AntlrInput::newInput(lang, *inputStream);
}

Input* Input::newStreamInput(const std::string& lang,
                             std::istream& input,
                             const std::string& name)
{
  AntlrInputStream* inputStream =
      AntlrInputStream::newStreamInputStream(input, name);
  return AntlrInput::newInput(lang, *inputStream);
}

Input* Input::newStringInput(const std::string& lang,
                             const std::string& str,
                             const std::string& name)
{
  AntlrInputStream *inputStream = AntlrInputStream::newStringInputStream(str, name);
  return AntlrInput::newInput(lang, *inputStream);
}

}  // namespace parser
}  // namespace cvc5
