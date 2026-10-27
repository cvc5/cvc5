; COMMAND-LINE: --produce-models
; EXPECT: sat
; EXPECT: ((A true))
(set-logic ALL)
(declare-const A Bool)
(declare-const b (_ BitVec 4))
(assert (or (and A (= b #b0001)) (and A (= b #b0000))))
(check-sat)
(get-value (A))
