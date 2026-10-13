; COMMAND-LINE: --incremental --rlimit-per=20000
; EXPECT: unknown
; EXPECT: (:reason-unknown resourceout)
; EXPECT: sat
; EXPECT: unsat
; The resource limit is reached while bit-blasting in a theory check. This is
; aborted by an exception caught in the bit-vector solver. The solver remains
; usable after popping.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(push 1)
(assert (= (bvmul x y) (bvmul y z)))
(assert (not (= x z)))
(assert (bvult x #x00001000))
(check-sat)
(get-info :reason-unknown)
(pop 1)
(push 1)
(assert (= x #x00000005))
(check-sat)
(assert (= x #x00000006))
(check-sat)
(pop 1)
