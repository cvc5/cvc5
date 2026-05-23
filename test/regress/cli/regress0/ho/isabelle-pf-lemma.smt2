; EXPECT: sat
; SCRUBBER: sed -n '1p'
(set-logic HO_ALL)
(set-option :produce-models true)
(declare-sort A 0)
(declare-fun P ((-> A A)) Bool)
(declare-fun f () (-> A A))

(assert (not (P f)))
(check-sat)
(get-model)
