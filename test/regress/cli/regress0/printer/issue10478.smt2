; EXPECT: sat
; EXPECT: ((x (seq.++ (seq.unit 1) (seq.unit 2))))
(set-option :produce-models true)
(set-logic ALL)
(declare-fun x () (Seq Int))
(assert (= x (seq.++ (seq.unit 1) (seq.unit 2))))
(check-sat)
(get-value (x))
