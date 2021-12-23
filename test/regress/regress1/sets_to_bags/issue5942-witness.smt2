; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)

(set-info :status sat)

(declare-fun r1 () Real)
(declare-fun st9 () (Bag String))
(declare-fun str2 () String)

(define-fun bag.is_singleton ((B (Bag String))) Bool
  (exists ((x String)) (= B (bag x1))))

(assert
  (bag.is_singleton
    (ite (= str2 (str.substr str2 0 (to_int r1))) st9 (as bag.empty (Bag String)))))

(check-sat)
