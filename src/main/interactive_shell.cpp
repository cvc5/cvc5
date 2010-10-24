/*********************                                                        */
/*! \file interactive_shell.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interactive shell for CVC4
 **/

#include <iostream>

#include "interactive_shell.h"
#include "expr/command.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"

using namespace std;

namespace CVC4 {

const string InteractiveShell::INPUT_FILENAME = "<shell>";

Command* InteractiveShell::readCommand() {
  /* Don't do anything if the input is closed. */
  if( d_in.eof() ) {
    return NULL;
  }

  /* If something's wrong with the input, there's nothing we can do. */
  if( !d_in.good() ) {
    throw ParserException("Interactive input broken.");
  }

  string input;

  /* Prompt the user for input. */
  d_out << "CVC4> " << flush;
  while(true) {
    stringbuf sb;
    string line;

    /* Read a line */
    d_in.get(sb,'\n');
    line = sb.str();
    // cout << "Input was '" << input << "'" << endl << flush;

    Assert( !(d_in.fail() && !d_in.eof()) || line.empty() );

    /* Check for failure. */
    if( d_in.fail() && !d_in.eof() ) {
      /* This should only happen if the input line was empty. */
      Assert( line.empty() );
      d_in.clear();
    }

    /* Strip trailing whitespace. */
    int n = line.length() - 1;
    while( !line.empty() && isspace(line[n]) ) { 
      line.erase(n,1); 
      n--;
    }

    /* If we hit EOF, we're done. */
    if( d_in.eof() ) {
      input += line;

      if( input.empty() ) {
        /* Nothing left to parse. */
        return NULL;
      }

      /* Some input left to parse, but nothing left to read. 
         Jump out of input loop. */
      break;
    }

    /* Extract the newline delimiter from the stream too */
    int c = d_in.get();
    Assert( c == '\n' );

    // cout << "Next char is '" << (char)c << "'" << endl << flush;

    input += line;
    
    /* If the last char was a backslash, continue on the next line. */
    n = input.length() - 1;
    if( !line.empty() && input[n] == '\\' ) {
      input[n] = '\n';
      d_out << "... > " << flush;
    } else {
      /* No continuation, we're done. */
      //cout << "Leaving input loop." << endl << flush;
      break;
    }
  }

  d_parser->setInput(Input::newStringInput(d_language,input,INPUT_FILENAME));
  // Parser *parser = 
  //   d_parserBuilder
  //       .withStringInput(input)
  //       .withStateFrom(d_lastParser)
  //       .build();

  /* There may be more than one command in the input. Build up a
     sequence. */
  CommandSequence *cmd_seq = new CommandSequence();
  Command *cmd;

  while( (cmd = d_parser->nextCommand()) ) {
    cmd_seq->addCommand(cmd);
  }

  // if( d_lastParser ) {
  //   delete d_lastParser;
  // }
  // d_lastParser = parser;

  return cmd_seq;
}

} // CVC4 namespace
