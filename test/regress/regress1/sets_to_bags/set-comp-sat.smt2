; COMMAND-LINE: --sets-ext --finite-model-find
; EXPECT: sat
(set-logic UFFS)
(set-info :status sat)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun x () (Bag U))


(assert (bag.subbag x (set.comprehension ((z U)) (not (= z a)) z)))

(assert (not (bag.count b x)))
(assert (bag.count c x))

(check-sat)
