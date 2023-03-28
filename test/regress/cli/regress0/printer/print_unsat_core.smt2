; COMMAND-LINE: --produce-unsat-cores -o unsat-core-benchmark
; EXPECT: unsat
; EXPECT: ;; unsat core
; EXPECT: (set-logic ALL)
; EXPECT: (declare-fun x () Int)
; EXPECT: (assert (and (> x 2) (< x 0)))
; EXPECT: (check-sat)
; EXPECT: ;; end unsat core
; EXPECT: (
; EXPECT: x20
; EXPECT: )
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (and (> x 2) (< x 0)) :named x20))
(assert (! (< y 0) :named y0))
(check-sat)
(get-unsat-core)
