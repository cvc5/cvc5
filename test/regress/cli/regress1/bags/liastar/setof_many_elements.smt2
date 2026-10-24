; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
; EXPECT: sat
; The model needs 40 distinct elements, more than the 32 fresh elements the
; model construction used to allow. The model checker cannot evaluate the
; resulting star-contains fact, hence quiet.
(set-logic HO_ALL)
(set-option :quiet true)
(declare-fun A () (Bag Int))
(assert (= (bag.card (bag.setof A)) 40))
(check-sat)
