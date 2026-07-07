; COMMAND-LINE: --finite-model-find --fmf-mbqi=trust -o incomplete
; EXPECT: (incomplete INCOMPLETE QUANTIFIERS_FMF)
; EXPECT: unknown
; EXPECT: (:reason-unknown incomplete)
(set-logic UF)
(declare-sort A 0)
(declare-fun le (A A) Bool)
(declare-fun p (A) Bool)
(declare-const w A)
(assert (forall ((x A)) (le x x)))
(assert (forall ((x A)) (=> (le x x) (not (p x)))))
(assert (p w))
(check-sat)
(get-info :reason-unknown)
