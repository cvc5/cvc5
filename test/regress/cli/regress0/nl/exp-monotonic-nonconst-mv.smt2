; COMMAND-LINE: --rlimit=10000
; EXPECT: unknown
;
; Reduced from regress2/nl/dumortier-050317.smt2. When checking monotonicity of
; exponential terms, an (exp t) term whose value was not assigned by the linear
; solver was previously identified by comparing its abstract model value to the
; term itself. That value is instead computed from the model values of the
; arguments, e.g. (exp c) for a constant c, which is not itself constant. Such
; terms were thus not filtered out, leading to an assertion failure.
;
; Note this benchmark does not terminate on its own, hence the resource limit.
(set-logic QF_NRAT)
(declare-fun t0 () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun y0 () Real)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (= t0 0.0))
(assert (or (not b0) (and (= y1 (* y0 (exp (- t1 t0)))) (or (= y1 y0) (not (= t0 t1))))))
(assert (or (not b1) (and (= y2 (* y1 (exp (- t2 t1)))) (or (= y2 y1) (not (= t1 t2))))))
(assert b1)
(check-sat)
