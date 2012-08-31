/*********************                                                        */
/*! \file model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_public.h"

#ifndef __CVC4__MODEL_H
#define __CVC4__MODEL_H

#include <iostream>
#include <vector>

namespace CVC4 {

class Command;

class Model
{
public:
  //types of commands that are recorded for get-model
  enum {
    COMMAND_DECLARE_SORT,       //DeclareTypeCommand
    COMMAND_DECLARE_FUN,        //DeclareFunctionCommand
    COMMAND_DECLARE_DATATYPES,  //DatatypeDeclarationCommand
  };
private:
  //list of commands that the model must report when calling get model
  std::vector< Command* > d_commands;
  std::vector< int > d_command_types;
public:
  /** add command */
  virtual void addCommand( Command* c, int c_type ){
    d_commands.push_back( c );
    d_command_types.push_back( c_type );
  }
  /** get number of commands to report */
  int getNumCommands() { return (int)d_commands.size(); }
  /** get command */
  Command* getCommand( int i ) { return d_commands[i]; }
  /** get type of command */
  int getCommandType( int i ) { return d_command_types[i]; }
public:
  virtual void toStream(std::ostream& out) = 0;
};/* class Model */

class ModelBuilder
{
public:
  ModelBuilder(){}
  virtual ~ModelBuilder(){}
  virtual void buildModel( Model* m, bool fullModel ) = 0;
};/* class ModelBuilder */

}/* CVC4 namespace */

#endif  /* __CVC4__MODEL_H */
