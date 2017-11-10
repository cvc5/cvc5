/*********************                                                        */
/*! \file sygus_print_callback.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus print callback functions
 **/

#include "cvc4_private.h"


#ifndef __CVC4__PRINTER__SYGUS_PRINT_CALLBACK_H
#define __CVC4__PRINTER__SYGUS_PRINT_CALLBACK_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace printer {

/** sygus let expression constructor printer
 * 
 * This class is used for printing sygus 
 * datatype constructor terms whose top symbol 
 * is a let expression.  
 * For example, for example: 
 *   A -> (let ((x B)) (+ A 1)) | x | (+ A A) | 0
 *   B -> 0 | 1
 * the first constructor for A takes as arguments 
 * (B,A) and has operator 
 *   (lambda ((y B) (z A)) (+ z 1))
 * CVC4's support for let expressions in grammars
 * is highly limited, since notice that the 
 * argument y : B is unused. 
 * 
 * For the above constructor, we have that 
 *   d_let_body is (+ z 1),
 *   d_sygus_let_args is { y, z },
 *   d_sygus_num_let_input_args is 1, since
 *     y is an original input argument of the 
 *     let expression, but z is not.
 */
class SygusLetExpressionConstructorPrinter : public SygusDatatypeConstructorPrinter
{
public:
  SygusLetExpressionPrinter( Node let_body, std::vector< Node >& let_args, unsigned ninput_args );
  ~SygusLetExpressionPrinter(){}
  /** print sygus term */
  virtual void toStreamSygus( std::ostream& out, Expr e,
                              OutputLanguage language = language::output::LANG_AUTO ) override;
private:
  /** let body of the sygus term */
  Node d_sygus_let_body;
  /** let arguments */
  std::vector< Node > d_sygus_let_args;
  /** number of arguments that are interpreted as input arguments */
  unsigned d_sygus_num_let_input_args;
  /** do string replace 
   * Replaces all occurrences of oldStr with newStr in str.
   */
  void doStrReplace(std::string& str, const std::string& oldStr, const std::string& newStr) const;
};

/** sygus named constructor printer
 * 
 * This callback is used for explicitly naming 
 * the builtin term that a sygus datatype constructor 
 * should be printed as. This is used for printing
 * terms in sygus grammars that involve defined 
 * functions. For example, for grammar :
 *   A -> f( A ) | 0
 * where f is defined as:
 *   (define-fun ((x Int)) Int (+ x 1))
 * this class can be used as a callback for printing 
 * the first sygus datatype constructor f, where we use
 * analog operator (lambda (x) (+ x 1)). 
 */
class SygusNamedConstructorPrinter : public SygusDatatypeConstructorPrinter
{
public:
  SygusNamedConstructorPrinter( std::string name );
  ~SygusNamedConstructorPrinter(){}
  /** print sygus term */
  virtual void toStreamSygus( std::ostream& out, Expr e,
                              OutputLanguage language = language::output::LANG_AUTO ) override;
private:
  /** the defined function name */
  std::string d_name;
};
  
} /* CVC4::printer namespace */
} /* CVC4 namespace */

#endif /* __CVC4__PRINTER__SYGUS_PRINT_CALLBACK_H */
