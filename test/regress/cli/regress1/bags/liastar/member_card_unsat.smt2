; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun e () Int)
(declare-fun f () Int)
; two distinct members are two rows of the star, so the cardinality is at least 2
(assert (bag.member e A))
(assert (bag.member f A))
(assert (not (= e f)))
(assert (= (bag.card A) 1))
(check-sat)
