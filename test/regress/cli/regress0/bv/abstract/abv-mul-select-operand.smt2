; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: unsat
; DISABLE-TESTER: proof
; The abstracted 64-bit bvmul has an array select inside its operand: the
; select is a foreign-theory leaf whose value is decided by the arrays theory.
; No 8-bit v satisfies 3 * v = 7 (mod 2^64) (3^-1 * 7 mod 2^64 exceeds 8 bits),
; so the formula is unsat.
(set-logic QF_ABV)
(declare-fun arr () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(assert (= (bvmul ((_ zero_extend 56) (select arr i)) (_ bv3 64)) (_ bv7 64)))
(check-sat)
