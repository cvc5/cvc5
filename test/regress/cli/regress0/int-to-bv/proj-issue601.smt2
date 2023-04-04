; EXPECT: sat
(set-logic ALL)
(set-option :solve-int-as-bv 3714675145)
(declare-sort u 0)
(define-fun f ((_f29_0 (Seq u))) (Seq u) _f29_0)
(check-sat)
