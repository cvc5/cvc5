; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic UFNIA)
(assert (exists ((k Int)) (not (=> (forall ((a Int) (b Int)) (! (= k (ite (= 0 (mod a 2)) 1 0)) :pattern (b))) false))))
(check-sat)
