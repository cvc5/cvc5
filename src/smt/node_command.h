/*********************                                                        */
/*! \file node_command.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datastructures used for printing commands internally.
 **
 ** Datastructures used for printing commands internally.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__NODE_COMMAND_H
#define CVC4__SMT__NODE_COMMAND_H

#include <string>

#include "expr/node.h"
#include "expr/type_node.h"
#include "options/language.h"

namespace CVC4 {

/** A node version of Command. DO NOT use this version unless there is a need
 * to buffer commands for later use (e.g., printing models). */
class NodeCommand
{
 public:
  /** Destructor */
  virtual ~NodeCommand();

  /** Print this NodeCommand to output stream */
  virtual void toStream(
      std::ostream& out,
      int toDepth = -1,
      bool types = false,
      size_t dag = 1,
      OutputLanguage language = language::output::LANG_AUTO) const = 0;

  /** Get a string representation of this NodeCommand */
  std::string toString() const;

  /** Clone this NodeCommand (make a shallow copy). */
  virtual NodeCommand* clone() const = 0;
};

std::ostream& operator<<(std::ostream& out, const NodeCommand& nc);

class DeclareFunctionNodeCommand : public NodeCommand
{
 public:
  DeclareFunctionNodeCommand(const std::string& id, Node fun, TypeNode type);
  void toStream(
      std::ostream& out,
      int toDepth = -1,
      bool types = false,
      size_t dag = 1,
      OutputLanguage language = language::output::LANG_AUTO) const override;
  NodeCommand* clone() const override;
  const Node& getFunction() const;
  bool getPrintInModel() const;
  bool getPrintInModelSetByUser() const;
  void setPrintInModel(bool p);

 private:
  std::string d_id;
  Node d_fun;
  TypeNode d_type;
  bool d_printInModel;
  bool d_printInModelSetByUser;
};

class DeclareDatatypeNodeCommand : public NodeCommand
{
 public:
  DeclareDatatypeNodeCommand(const std::vector<TypeNode>& datatypes);
  void toStream(
      std::ostream& out,
      int toDepth = -1,
      bool types = false,
      size_t dag = 1,
      OutputLanguage language = language::output::LANG_AUTO) const override;
  NodeCommand* clone() const override;

 private:
  std::vector<TypeNode> d_datatypes;
};

class DeclareTypeNodeCommand : public NodeCommand
{
 public:
  DeclareTypeNodeCommand(const std::string& id, size_t arity, TypeNode type);
  void toStream(
      std::ostream& out,
      int toDepth = -1,
      bool types = false,
      size_t dag = 1,
      OutputLanguage language = language::output::LANG_AUTO) const override;
  NodeCommand* clone() const override;
  const std::string getSymbol() const;
  const TypeNode& getType() const;

 private:
  std::string d_id;
  size_t d_arity;
  TypeNode d_type;
};

class DefineFunctionNodeCommand : public NodeCommand
{
 public:
  DefineFunctionNodeCommand(const std::string& id,
                            Node fun,
                            const std::vector<Node>& formals,
                            Node formula);
  void toStream(
      std::ostream& out,
      int toDepth = -1,
      bool types = false,
      size_t dag = 1,
      OutputLanguage language = language::output::LANG_AUTO) const override;
  NodeCommand* clone() const override;

 private:
  std::string d_id;
  Node d_fun;
  std::vector<Node> d_formals;
  Node d_formula;
};

}  // namespace CVC4

#endif /* CVC4__SMT__NODE_COMMAND_H */