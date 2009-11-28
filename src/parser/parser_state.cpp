/*
 * parser_state.cpp
 *
 *  Created on: Nov 20, 2009
 *      Author: dejan
 */

#include "parser_state.h"
#include "parser_exception.h"
#include <sstream>

using namespace std;

namespace CVC4
{

namespace parser
{

int ParserState::read(char* buffer, int size)
{
  if (d_input_stream) {
    // Read the characters and count them in result
    d_input_stream->read(buffer, size);
    return d_input_stream->gcount();
  } else return 0;
}

ParserState::ParserState() :
  d_uid(0), d_prompt_main("CVC>"), d_prompt_continue("- "), d_prompt("CVC"), d_input_line(0), d_done(false)
{

}

int ParserState::parseError(const std::string& s)
{
  throw new ParserException(s);
}

string ParserState::getNextUniqueID()
{
  ostringstream ss;
  ss << d_uid++;
  return ss.str();
}

string ParserState::getCurrentPrompt() const
{
  return d_prompt;
}

void ParserState::setPromptMain()
{
  d_prompt = d_prompt_main;
}

void ParserState::setPromptNextLine()
{
  d_prompt = d_prompt_continue;
}

void ParserState::increaseLineNumber()
{
  ++d_input_line;
  if (d_interactive) {
    std::cout << getCurrentPrompt();
    setPromptNextLine();
  }
}

int ParserState::getLineNumber() const
{
  return d_input_line;
}

std::string ParserState::getFileName() const
{
  return d_file_name;
}

} // End namespace parser

} // End namespace CVC3

