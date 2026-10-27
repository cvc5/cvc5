; COMMAND-LINE: --produce-proofs -o unsat-core-lemmas-benchmark
; EXPECT: unsat
; EXPECT: ;; unsat core + lemmas
; EXPECT: (set-logic ALL)
; EXPECT: (declare-fun x () Int)
; EXPECT: (assert (and (> x 2) (< x 0)))
; EXPECT: (assert (or (not (>= x 3)) (>= x 0)))
; EXPECT: (check-sat)
; EXPECT: ;; end unsat core + lemmas
; EXPECT: (
; EXPECT: (or (not (>= x 3)) (>= x 0))
; EXPECT: )
(set-logic ALL)
(set-option :produce-proofs true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (and (> x 2) (< x 0)) :named x20))
(assert (! (< y 0) :named y0))
(check-sat)
(get-unsat-core-lemmas)
