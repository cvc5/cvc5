; COMMAND-LINE: --dump-instantiations --print-inst-full
; SCRUBBER: sed -e 's/@quantifiers_skolemize_.* )$/@quantifiers_skolemize_TERM )/'
; EXPECT: unsat
; EXPECT: (skolem (forall ((x Int)) (or (P x) (Q x)))
; EXPECT:   ( @quantifiers_skolemize_TERM )
; EXPECT: )
; EXPECT: (instantiations (forall ((x Int)) (P x))
; EXPECT:   ( @quantifiers_skolemize_TERM )
; EXPECT: )
; disable proofs since it impacts what is relevant (e.g. the skolem lemmas)
; DISABLE-TESTER: proof
(set-logic UFLIA)
(set-info :status unsat)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (exists ((x Int)) (and (not (P x)) (not (Q x)))))
(check-sat)
