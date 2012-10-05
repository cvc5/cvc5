(*********************                                                        **
**! \file SimpleVC.ml
*** \verbatim
*** Original author: mdeters
*** Major contributors: none
*** Minor contributors (to current version): none
*** This file is part of the CVC4 prototype.
*** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
*** Courant Institute of Mathematical Sciences
*** New York University
*** See the file COPYING in the top-level source directory for licensing
*** information.\endverbatim
***
*** \brief A simple demonstration of the OCaml interface
***
*** A simple demonstration of the OCaml interface.  Compare to the
*** C++ interface in simple_vc_cxx.cpp; they are quite similar.
***
*** To run, use something like:
***
***   LD_LIBRARY_PATH=../builds/src/bindings/ocaml/.libs \
***     ../builds/src/bindings/cvc4_ocaml_top -I ../builds/src/bindings/ocaml \
***     SimpleVC.ml
***
*** After you "make install" CVC4, it's much easier; the cvc4_ocaml_top goes in
*** $prefix/bin, and it's automatically set up the load the .cmo and .cmi files
*** from $prefix/lib/ocaml/cvc4, in which they get installed.  Then you just
*** have to: cvc4_ocaml_top -I $prefix/lib/ocaml/cvc4
***)

open Swig
open CVC4

let em = new_ExprManager '()
let smt = new_SmtEngine(em)

(* Prove that for integers x and y:
 *   x > 0 AND y > 0  =>  2x + y >= 3 *)

let integer = em->integerType()

let x = em->mkVar(integer) (* em->mkVar("x", integer) *)
let y = em->mkVar(integer) (* em->mkVar("y", integer) *)
let integerZero = new_Integer '("0", 10)
let zero = em->mkConst(integerZero)

(* OK, this is really strange.  We can call mkExpr(36, ...) for
 * example, with the int value of the operator Kind we want,
 * or we can compute it.  But if we compute it, we have to rip
 * it out of its C_int, then wrap it again a C_int, in order
 * for the parser to make it go through. *)
let geq = C_int (get_int (enum_to_int `Kind_t (``GEQ)))
let gt = C_int (get_int (enum_to_int `Kind_t (``GT)))
let mult = C_int (get_int (enum_to_int `Kind_t (``MULT)))
let plus = C_int (get_int (enum_to_int `Kind_t (``PLUS)))
let and_kind = C_int (get_int (enum_to_int `Kind_t (``AND)))
let implies = C_int (get_int (enum_to_int `Kind_t (``IMPLIES)))

(* gt = 35, but the parser screws up if we put "geq" what follows *)
let x_positive = em->mkExpr(gt, x, zero)
let y_positive = em->mkExpr(gt, y, zero)

let integerTwo = new_Integer '("2", 10)
let two = em->mkConst(integerTwo)
let twox = em->mkExpr(mult, two, x)
let twox_plus_y = em->mkExpr(plus, twox, y)

let integerThree = new_Integer '("3", 10)
let three = em->mkConst(integerThree)
let twox_plus_y_geq_3 = em->mkExpr(geq, twox_plus_y, three)

let lhs = em->mkExpr(and_kind, x_positive, y_positive)

(* This fails for some reason. *)
(* let rhs = new_Expr(twox_plus_y_geq_3)
   let formula = new_Expr(lhs)->impExpr(rhs) *)

let formula = em->mkExpr(implies, lhs, twox_plus_y_geq_3)

let bformula = new_Expr(formula) in

print_string "Checking validity of formula " ;
print_string (get_string (formula->toString ())) ;
print_string " with CVC4." ;
print_newline () ;
print_string "CVC4 should report VALID." ;
print_newline () ;
print_string "Result from CVC4 is: " ;
print_string (get_string (smt->query(bformula)->toString ())) ;
print_newline ()
;;
