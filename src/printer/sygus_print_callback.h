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

<<<<<<< HEAD
#include "cvc4_public.h"
=======
#include "cvc4_private.h"
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741

#ifndef __CVC4__PRINTER__SYGUS_PRINT_CALLBACK_H
#define __CVC4__PRINTER__SYGUS_PRINT_CALLBACK_H

#include <vector>

<<<<<<< HEAD
#include "expr/expr.h"
#include "expr/datatype.h"
=======
#include "expr/node.h"
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741

namespace CVC4 {
namespace printer {

<<<<<<< HEAD
/** sygus expression constructor printer
 *
 * This class is used for printing sygus datatype constructor terms whose top 
 * symbol is an expression, such as a custom defined lambda. For example, for 
 * sygus grammar: 
 *    A -> (+ x A B) | x | y
 *    B -> 0 | 1
 * The first constructor, call it C_f for A takes two arguments (A, B) and has 
 * sygus operator
 *   (lambda ((z Int) (w Int)) (+ x z w))
 * For this operator, we set a print callback that prints, e.g. the term 
 *   C_f( t1, t2 )
 * is printed as:
 *   "(+ x [out1] [out2])"
 * where out1 is the result of p->toStreamSygus(out,t1) and
 *       out2 is the result of p->toStreamSygus(out,t2).
 */
class CVC4_PUBLIC SygusExprPrintCallback : public SygusPrintCallback
{
 public:
  SygusExprPrintCallback(Expr body, std::vector<Expr>& args);
  ~SygusExprPrintCallback() {}
  /** print sygus term e on output out using printer p */
  virtual void toStreamSygus(const Printer* p,
                             std::ostream& out,
                             Expr e) const override;

 protected:
  /** body of the sygus term */
  Expr d_body;
  /** arguments */
  std::vector<Expr> d_args;
  /** body argument */
  int d_body_argument;
  /** do string replace
   * Replaces all occurrences of oldStr with newStr in str.
   */
  void doStrReplace(std::string& str,
                    const std::string& oldStr,
                    const std::string& newStr) const;
};
  
=======
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741
/** sygus let expression constructor printer
 *
 * This class is used for printing sygus
 * datatype constructor terms whose top symbol
 * is a let expression.
 * For example, for grammar:
 *   A -> (let ((x B)) (+ A 1)) | x | (+ A A) | 0
 *   B -> 0 | 1
 * the first constructor for A takes as arguments
<<<<<<< HEAD
 * (B,A) and has sygus operator
 *   (lambda ((y Int) (z Int)) (+ z 1))
=======
 * (B,A) and has operator
 *   (lambda ((y B) (z A)) (+ z 1))
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741
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
<<<<<<< HEAD
class CVC4_PUBLIC SygusLetExprPrintCallback : public SygusExprPrintCallback
{
 public:
  SygusLetExprPrintCallback(Expr let_body,
                                       std::vector<Expr>& let_args,
                                      unsigned ninput_args);
  ~SygusLetExprPrintCallback() {}
=======
class SygusLetExpressionConstructorPrinter
    : public SygusDatatypeConstructorPrinter
{
 public:
  SygusLetExpressionPrinter(Node let_body,
                            std::vector<Node>& let_args,
                            unsigned ninput_args);
  ~SygusLetExpressionPrinter() {}
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741
  /** print sygus term e on output out using printer p */
  virtual void toStreamSygus(const Printer* p,
                             std::ostream& out,
                             Expr e) const override;

 private:
<<<<<<< HEAD
  /** number of arguments that are interpreted as input arguments */
  unsigned d_num_let_input_args;
=======
  /** let body of the sygus term */
  Node d_sygus_let_body;
  /** let arguments */
  std::vector<Node> d_sygus_let_args;
  /** number of arguments that are interpreted as input arguments */
  unsigned d_sygus_num_let_input_args;
  /** do string replace
   * Replaces all occurrences of oldStr with newStr in str.
   */
  void doStrReplace(std::string& str,
                    const std::string& oldStr,
                    const std::string& newStr) const;
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741
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
<<<<<<< HEAD
class CVC4_PUBLIC SygusNamedPrintCallback : public SygusPrintCallback
{
 public:
  SygusNamedPrintCallback(std::string name);
  ~SygusNamedPrintCallback() {}
=======
class SygusNamedConstructorPrinter : public SygusDatatypeConstructorPrinter
{
 public:
  SygusNamedConstructorPrinter(std::string name);
  ~SygusNamedConstructorPrinter() {}
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741
  /** print sygus term e on output out using printer p */
  virtual void toStreamSygus(const Printer* p,
                             std::ostream& out,
                             Expr e) const override;

 private:
  /** the defined function name */
  std::string d_name;
};

/** sygus empty printer
 *
 * This callback is used for printing constructors whose operators are
 * implicit, such as identity functions. For example, for grammar :
 *   A -> B
 *   B -> x | 0 | 1
 * The first constructor of A, call it cons, has sygus operator (lambda (x) x).
 * Call toStreamSygus on cons( t ) should call toStreamSygus on t directly.
 */
<<<<<<< HEAD
class CVC4_PUBLIC SygusEmptyPrintCallback : public SygusPrintCallback
{
 public:
  SygusEmptyPrintCallback(){}
  ~SygusEmptyPrintCallback() {}
=======
class SygusEmptyConstructorPrinter : public SygusDatatypeConstructorPrinter
{
 public:
  SygusEmptyConstructorPrinter(std::string name);
  ~SygusEmptyConstructorPrinter() {}
>>>>>>> 6c6f4e23aea405a812b1c6a3dd4d80696eb34741
  /** print sygus term e on output out using printer p */
  virtual void toStreamSygus(const Printer* p,
                             std::ostream& out,
                             Expr e) const override;
};

} /* CVC4::printer namespace */
} /* CVC4 namespace */

#endif /* __CVC4__PRINTER__SYGUS_PRINT_CALLBACK_H */
