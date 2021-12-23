; COMMAND-LINE: --sets-ext --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun x () (Bag U))
(define-fun bag.member ((e U) (B (Bag U))) Bool (>= (bag.count e B) 1))

(assert (bag.subbag x (bag.comprehension ((z U)) (not (= z a)) z)))

(assert (not (bag.member b x)))
(assert (bag.member c x))

(check-sat)
