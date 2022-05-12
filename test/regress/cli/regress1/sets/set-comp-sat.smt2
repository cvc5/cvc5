; COMMAND-LINE: --sets-ext --finite-model-find
; EXPECT: sat
(set-logic UFFS)
(set-info :status sat)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun x () (Set U))


(assert (set.subset x (set.comprehension ((z U)) (not (= z a)) z)))

(assert (not (set.member b x)))
(assert (set.member c x))

(check-sat)
