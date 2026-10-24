; REQUIRES: normaliz
; DISABLE-TESTER: proof
; the fresh elements of the elements mode are terms asserted distinct from the
; known ones, which Bool refutes by itself
; COMMAND-LINE: --bags-to-liastar --bags-liastar-model=elements
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Bool))
(assert (= (bag.count true A) 1))
(assert (= (bag.count false A) 1))
(assert (= (bag.card A) 3))
(check-sat)
