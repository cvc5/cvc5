/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datastructures used for printing commands internally.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__NODE_COMMAND_H
#define CVC5__SMT__NODE_COMMAND_H

#include <string>

#include "expr/node.h"
#include "expr/type_node.h"
#include "options/language.h"

namespace cvc5 {

/**
 * A node version of Command. DO NOT use this version unless there is a need
 * to buffer commands for later use (e.g., printing models).
 */
class NodeCommand
{
 public:
  /** Destructor */
  virtual ~NodeCommand();

  /** Print this NodeCommand to output stream */
  virtual void toStream(std::ostream& out,
                        int toDepth = -1,
                        size_t dag = 1,
                        Language language = Language::LANG_AUTO) const = 0;

  /** Get a string representation of this NodeCommand */
  std::string toString() const;

  /** Clone this NodeCommand (make a shallow copy). */
  virtual NodeCommand* clone() const = 0;
};

std::ostream& operator<<(std::ostream& out, const NodeCommand& nc);

/**
 * Declare n-ary function symbol.
 * SMT-LIB: ( declare-fun <id> ( <type.getArgTypes()> ) <type.getRangeType()> )
 */
class DeclareFunctionNodeCommand : public NodeCommand
{
 public:
  DeclareFunctionNodeCommand(const std::string& id, Node fun, TypeNode type);
  void toStream(std::ostream& out,
                int toDepth = -1,
                size_t dag = 1,
                Language language = Language::LANG_AUTO) const override;
  NodeCommand* clone() const override;
  const Node& getFunction() const;

 private:
  std::string d_id;
  Node d_fun;
  TypeNode d_type;
};

/**
 * Create datatype sort.
 * SMT-LIB: ( declare-datatypes ( <datatype decls>{n+1} ) ( <datatypes>{n+1} ) )
 */
class DeclareDatatypeNodeCommand : public NodeCommand
{
 public:
  DeclareDatatypeNodeCommand(const std::vector<TypeNode>& datatypes);
  void toStream(std::ostream& out,
                int toDepth = -1,
                size_t dag = 1,
                Language language = Language::LANG_AUTO) const override;
  NodeCommand* clone() const override;

 private:
  std::vector<TypeNode> d_datatypes;
};

/**
 * Declare uninterpreted sort.
 * SMT-LIB: ( declare-sort <id> <arity> )
 */
class DeclareTypeNodeCommand : public NodeCommand
{
 public:
  DeclareTypeNodeCommand(const std::string& id, size_t arity, TypeNode type);
  void toStream(std::ostream& out,
                int toDepth = -1,
                size_t dag = 1,
                Language language = Language::LANG_AUTO) const override;
  NodeCommand* clone() const override;
  const std::string getSymbol() const;
  const TypeNode& getType() const;

 private:
  std::string d_id;
  size_t d_arity;
  TypeNode d_type;
};

/**
 * Define n-ary function.
 * SMT-LIB: ( define-fun <id> ( <formals> ) <fun.getType()> <formula> )
 */
class DefineFunctionNodeCommand : public NodeCommand
{
 public:
  DefineFunctionNodeCommand(const std::string& id,
                            Node fun,
                            const std::vector<Node>& formals,
                            Node formula);
  void toStream(std::ostream& out,
                int toDepth = -1,
                size_t dag = 1,
                Language language = Language::LANG_AUTO) const override;
  NodeCommand* clone() const override;

 private:
  std::string d_id;
  Node d_fun;
  std::vector<Node> d_formals;
  Node d_formula;
};

}  // namespace cvc5

#endif /* CVC5__SMT__NODE_COMMAND_H */
