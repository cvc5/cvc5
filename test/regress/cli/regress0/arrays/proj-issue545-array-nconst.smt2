; SCRUBBER: sed -e 's/((f.*/((f/g'
; EXPECT: sat
; EXPECT: ((f
(set-logic ALL)
(set-option :produce-models true)
(declare-sort u 0)
(declare-const x u)
(define-fun f ((_f5_1 u) (_f5_2 Bool)) u (ite _f5_2 _f5_1 x))
(check-sat)
(get-value (f))
