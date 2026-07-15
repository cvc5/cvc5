; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: unsat
; DISABLE-TESTER: proof
; QF_ABV coverage for the shape that exposed abstraction below foreign-theory
; terms: the abstracted bvmul feeds the two select indices, which are
; syntactically distinct but provably equal (y is forced to 1 by the
; inequalities, but not by a top-level substitution), so the read values
; contradict. The full-size witness for the soundness bug is
; regress2/bv/abstract/abv-klee-select-index.smt2.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (bvule y (_ bv1 8)))
(assert (bvuge y (_ bv1 8)))
(assert (= (select a (bvadd (bvmul x s) (_ bv1 8))) (_ bv10 8)))
(assert (= (select a (bvadd (bvmul x s) y)) (_ bv11 8)))
(check-sat)
