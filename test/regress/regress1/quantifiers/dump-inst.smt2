; COMMAND-LINE: --dump-instantiations
; SCRUBBER: sed -e 's/skv_.* )$/skv_TERM )/'
; EXPECT: unsat
; EXPECT: (skolem (forall ((x Int)) (or (P x) (Q x)) )
; EXPECT:   ( skv_TERM )
; EXPECT: )
; EXPECT: (instantiations (forall ((x Int)) (P x) )
; EXPECT:   ( skv_TERM )
; EXPECT: )
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (exists ((x Int)) (and (not (P x)) (not (Q x)))))
(check-sat)
