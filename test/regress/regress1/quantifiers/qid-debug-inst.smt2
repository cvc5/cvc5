; COMMAND-LINE: --debug-inst
; EXPECT: (num-instantiations myQuant1 1)
; EXPECT: (num-instantiations myQuant2 1)
; EXPECT: unsat

(set-logic UFLIA)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (! (P x) :qid |myQuant1|)))
(assert (forall ((x Int)) (! (=> (P x) (Q x)) :qid |myQuant2|)))
(assert (P 5))
(assert (not (Q 5)))
(check-sat)
