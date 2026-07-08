; EXPECT: sat
; Two abstracted real-to-FP conversions sharing the same non-leaf real
; argument: exercises TheoryFp::purifyArgument's per-argument caching (the
; second registration reuses the purification skolem and does not re-send the
; defining equality).
(set-logic QF_FPLRA)
(declare-const x Real)
(declare-const a Float32)
(declare-const b Float64)
(assert (= a ((_ to_fp 8 24) RNE (+ x 1.0))))
(assert (= b ((_ to_fp 11 53) RNE (+ x 1.0))))
(assert (fp.gt a ((_ to_fp 8 24) RNE 2.0)))
(assert (fp.lt b ((_ to_fp 11 53) RNE 100.0)))
(check-sat)
