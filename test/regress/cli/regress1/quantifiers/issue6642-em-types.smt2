; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun b () String)
(assert (forall ((c (Seq Int))) (exists ((a String)) (and (= 1 (seq.len c)) (not (= b a))))))
(check-sat)
