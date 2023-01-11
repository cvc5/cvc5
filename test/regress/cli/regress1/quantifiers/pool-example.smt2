; COMMAND-LINE: --pool-inst
; EXPECT: unsat
(set-logic ALL)
(declare-pool L Int ())

(declare-fun P (Int) Bool)

(assert (not (=
(forall ((x Int)) (! 
  (P x)
  :skolem-add-to-pool ((- x 100) L) :pool (L) ))
(forall ((x Int)) (!
  (P (+ x 100))
  :skolem-add-to-pool ((+ x 100) L) :pool (L) )
))))

(check-sat)
