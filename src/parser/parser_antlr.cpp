/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Parser state implementation.
 */

#include "parser/parser_antlr.h"

#include <cvc5/cvc5.h>

#include <clocale>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <unordered_set>

#include "base/check.h"
#include "base/output.h"
#include "expr/kind.h"
#include "parser/api/cpp/command.h"
#include "parser/input.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2_input.h"

using namespace std;

namespace cvc5 {
namespace parser {

class Parser::IncludeFileCache
{
 public:
  IncludeFileCache() {}
  ~IncludeFileCache()
  {
    for (size_t i = 0, isize = d_inCreated.size(); i < isize; i++)
    {
      d_inCreated[i]->free(d_inCreated[i]);
    }
  }
  std::vector<pANTLR3_INPUT_STREAM> d_inCreated;
};

Parser::Parser() : d_done(true), d_canIncludeFile(true) {}

Parser::~Parser()
{
}

void Parser::preemptCommand(std::unique_ptr<Command> cmd)
{
  d_commandQueue.push_back(std::move(cmd));
}
std::unique_ptr<Command> Parser::nextCommand()
{
  Trace("parser") << "nextCommand()" << std::endl;
  std::unique_ptr<Command> cmd;
  if (!d_commandQueue.empty())
  {
    cmd = std::move(d_commandQueue.front());
    d_commandQueue.pop_front();
    setDone(cmd == NULL);
  }
  else
  {
    try
    {
      cmd = d_input->parseCommand();
      d_commandQueue.push_back(std::move(cmd));
      cmd = std::move(d_commandQueue.front());
      d_commandQueue.pop_front();
      setDone(cmd == NULL);
    }
    catch (ParserException& e)
    {
      setDone();
      throw;
    }
    catch (exception& e)
    {
      setDone();
      parseError(e.what());
    }
  }
  Trace("parser") << "nextCommand() => " << cmd.get() << std::endl;
  return cmd;
}

cvc5::Term Parser::nextExpression()
{
  Trace("parser") << "nextExpression()" << std::endl;
  cvc5::Term result;
  if (!done())
  {
    try
    {
      result = d_input->parseExpr();
      setDone(result.isNull());
    }
    catch (ParserException& e)
    {
      setDone();
      throw;
    }
    catch (exception& e)
    {
      setDone();
      parseError(e.what());
    }
  }
  Trace("parser") << "nextExpression() => " << result << std::endl;
  return result;
}

void Parser::enableChecks() { getState()->enableChecks(); }

void Parser::disableChecks() { getState()->disableChecks(); }

/* The include are managed in the lexer but called in the parser */
// Inspired by http://www.antlr3.org/api/C/interop.html

bool newInputStream(std::string fileName,
                    pANTLR3_LEXER lexer,
                    std::vector<pANTLR3_INPUT_STREAM>& inc)
{
  Trace("parser") << "Including " << fileName << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM in;
#ifdef CVC5_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8)fileName.c_str());
#else  /* CVC5_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8)fileName.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC5_ANTLR3_OLD_INPUT_STREAM */
  if (in == NULL)
  {
    Trace("parser") << "Can't open " << fileName << std::endl;
    return false;
  }
  // Same thing as the predefined PUSHSTREAM(in);
  lexer->pushCharStream(lexer, in);
  // restart it
  // lexer->rec->state->tokenStartCharIndex  = -10;
  // lexer->emit(lexer);

  // Note that the input stream is not closed when it EOFs, I don't bother
  // to do it here, but it is up to you to track streams created like this
  // and destroy them when the whole parse session is complete. Remember that
  // you don't want to do this until all tokens have been manipulated all the
  // way through your tree parsers etc as the token does not store the text it
  // just refers back to the input stream and trying to get the text for it will
  // abort if you close the input stream too early.
  //
  inc.push_back(in);

  // TODO what said before
  return true;
}

Parser::IncludeFileCache* Parser::getIncludeFileCache()
{
  if (d_incCache == nullptr)
  {
    d_incCache.reset(new IncludeFileCache);
  }
  return d_incCache.get();
}

void Parser::includeSmt2File(const std::string& filename)
{
  // security for online version
  if (!canIncludeFile())
  {
    parseError("include-file feature was disabled for this run.");
  }

  // Get the lexer
  AntlrInput* ai = static_cast<AntlrInput*>(getInput());
  pANTLR3_LEXER lexer = ai->getAntlr3Lexer();
  // get the name of the current stream "Does it work inside an include?"
  const std::string inputName = ai->getInputStreamName();

  // Find the directory of the current input file
  std::string path;
  size_t pos = inputName.rfind('/');
  if (pos != std::string::npos)
  {
    path = std::string(inputName, 0, pos + 1);
  }
  path.append(filename);
  IncludeFileCache* ifc = getIncludeFileCache();
  if (!newInputStream(path, lexer, ifc->d_inCreated))
  {
    parseError("Couldn't open include file `" + path + "'");
  }
}

void Parser::includeTptpFile(const std::string& fileName,
                             const std::string& tptpDir)
{
  // security for online version
  if (!canIncludeFile())
  {
    parseError("include-file feature was disabled for this run.");
  }

  // Get the lexer
  AntlrInput* ai = static_cast<AntlrInput*>(getInput());
  pANTLR3_LEXER lexer = ai->getAntlr3Lexer();

  // push the inclusion scope; will be popped by our special popCharStream
  // would be necessary for handling symbol filtering in inclusions
  // pushScope();

  // get the name of the current stream "Does it work inside an include?"
  const std::string inputName = ai->getInputStreamName();

  // Test in the directory of the actual parsed file
  std::string currentDirFileName;
  if (inputName != "<stdin>")
  {
    // TODO: Use dirname or Boost::filesystem?
    size_t pos = inputName.rfind('/');
    if (pos != std::string::npos)
    {
      currentDirFileName = std::string(inputName, 0, pos + 1);
    }
    currentDirFileName.append(fileName);
    IncludeFileCache* ifc = getIncludeFileCache();
    if (newInputStream(currentDirFileName, lexer, ifc->d_inCreated))
    {
      return;
    }
  }
  else
  {
    currentDirFileName = "<unknown current directory for stdin>";
  }

  if (tptpDir.empty())
  {
    parseError("Couldn't open included file: " + fileName
               + " at " + currentDirFileName + " and the TPTP directory is not specified (environment variable TPTP)");
  };

  std::string tptpDirFileName = tptpDir + fileName;
  IncludeFileCache* ifc = getIncludeFileCache();
  if (!newInputStream(tptpDirFileName, lexer, ifc->d_inCreated))
  {
    parseError("Couldn't open included file: " + fileName + " at "
               + currentDirFileName + " or " + tptpDirFileName);
  }
}

}  // namespace parser
}  // namespace cvc5
