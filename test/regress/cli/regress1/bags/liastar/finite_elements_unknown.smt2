; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star assumes an element for every row it needs, and Bool has only two, so
; the subsolver mode marks the model unsound instead of answering sat
; COMMAND-LINE: --bags-to-liastar
; EXPECT: unknown
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Bool))
(assert (= (bag.count true A) 1))
(assert (= (bag.count false A) 1))
(assert (= (bag.card A) 3))
(check-sat)
