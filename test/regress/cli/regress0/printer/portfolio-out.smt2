; COMMAND-LINE: --use-portfolio -o portfolio
; SCRUBBER: grep -o "portfolio-success"
; EXPECT: portfolio-success
; EXIT: 0
; DISABLE-TESTER: dump
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (not (P 10)))
(check-sat)
