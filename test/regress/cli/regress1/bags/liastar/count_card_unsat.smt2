; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun e () Int)
; the count term of e is a row of the star, so it is bounded by the cardinality
(assert (= (bag.count e A) 2))
(assert (= (bag.card A) 1))
(check-sat)
