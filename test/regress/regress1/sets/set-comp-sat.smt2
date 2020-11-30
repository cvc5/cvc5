; COMMAND-LINE: --sets-ext --finite-model-find
; EXPECT: sat
(set-logic UFFS)
(set-info :status sat)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun x () (Set U))


(assert (subset x (comprehension ((z U)) (not (= z a)) z)))

(assert (not (member b x)))
(assert (member c x))

(check-sat)
