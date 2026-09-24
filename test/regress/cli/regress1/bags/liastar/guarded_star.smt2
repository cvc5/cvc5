; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the star constrains the cardinalities, not the bag values
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun C () (Bag Int))
; sat with A = C = {x} and B = bag.empty. The body of the star translates the
; bag equalities of the branch it was built in, so the star must be asserted
; guarded by them: an unguarded star built in the branch where (= A B) holds
; would keep forcing the multiplicities of A and B to be equal at every
; element, hence (= (bag.card A) (bag.card B)), and would refute this input.
(assert (or (= A B) (= A C)))
(assert (= (bag.card A) 1))
(assert (= (bag.card B) 0))
(assert (= (bag.card C) 1))
(check-sat)
