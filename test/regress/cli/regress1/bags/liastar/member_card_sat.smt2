; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status sat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
(declare-fun e () Int)
(declare-fun f () Int)
; the members are rows of the star and the model needs one more element, e.g.
; A = {e}, B = {f, e} or e = f with A = {e}, B = {e, e}
(assert (bag.member e A))
(assert (bag.member f B))
(assert (= (bag.card (bag.union_disjoint A B)) 3))
(assert (= (bag.card (bag.inter_min A B)) 1))
(check-sat)
