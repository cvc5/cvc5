; REQUIRES: normaliz
; DISABLE-TESTER: proof
; a guarded star (=> premises star) leaves the star literal free when the
; premises are false, and --debug-check-models cannot evaluate a star atom
; the SAT solver assigned false, so it reports it as possibly violated
; DISABLE-TESTER: model
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
; sat with a bag of cardinality 3 whose elements add up to 10
(assert (= (bag.card A) 3))
(assert (= (bag.fold (lambda ((x Int) (y Int)) (+ x y)) 0 A) 10))
(check-sat)
