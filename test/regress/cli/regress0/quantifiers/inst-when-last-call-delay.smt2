; COMMAND-LINE: --inst-when=last-call-delay
; EXPECT: unsat
; Nonlinear arithmetic sends lemmas at last call effort, which delays
; instantiation in later rounds.
(set-logic UFNIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (forall ((z Int)) (! (> (f z) 0) :pattern ((f z)))))
(assert (= (f (* x y)) (- (* x x))))
(check-sat)
