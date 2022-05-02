; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LIA)

(declare-fun i () Int)
(declare-fun j () Int)

(assert (> (+ i j) 1))
(assert (< i 1))
(assert (< j 1))

(check-sat)
