/*********************                                                        */
/*! \file input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A super-class for input language parsers.
 **
 ** A super-class for input language parsers
 **/

// This must be included first.
#include "parser/antlr_input.h"

#include "parser/input.h"

#include "base/output.h"
#include "expr/type.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
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

Input* Input::newFileInput(InputLanguage lang,
                           const std::string& filename,
                           bool useMmap)
{
  AntlrInputStream *inputStream = 
    AntlrInputStream::newFileInputStream(filename, useMmap);
  return AntlrInput::newInput(lang, *inputStream);
}

Input* Input::newStreamInput(InputLanguage lang,
                             std::istream& input,
                             const std::string& name,
                             bool lineBuffered)
{
  AntlrInputStream *inputStream =
    AntlrInputStream::newStreamInputStream(input, name, lineBuffered);
  return AntlrInput::newInput(lang, *inputStream);
}

Input* Input::newStringInput(InputLanguage lang,
                             const std::string& str,
                             const std::string& name)
{
  AntlrInputStream *inputStream = AntlrInputStream::newStringInputStream(str, name);
  return AntlrInput::newInput(lang, *inputStream);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
